module Language.Reflection.Monomorphisation2

import public Data.SnocList
import public Language.Reflection
import public Language.Reflection.Syntax
import public Language.Reflection.Types
import public Language.Reflection.Pretty
import public Language.Reflection.Util
import public Language.Reflection.Types
import public Language.Reflection.TT
import public Language.Reflection.TTImp
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops
import public Data.List1
import public Data.Vect
import public Data.List
import public Data.Either
import public Data.SortedMap
import public Data.SortedSet
import public Data.SortedMap.Dependent
import public Text.PrettyPrint.Bernardy.Interface
import public Text.PrettyPrint.Bernardy.Core
import public Language.Reflection.Unification
import public Control.Monad.Reader.Tuple

%language ElabReflection

||| Valid type task interface
|||
||| Auto-implemented by any Type or any function that returns Type.
public export
interface TypeTask (t : Type) where

public export
TypeTask Type

public export
TypeTask b => TypeTask (a -> b)

||| Extract contents of a lambda
taskInvocation : Elaboration m => TTImp -> m TTImp
taskInvocation (ILam _ _ _ _ _ r) = taskInvocation r
taskInvocation x@(IApp _ _ _) = pure x
taskInvocation x@(INamedApp _ _ _ _) = pure x
taskInvocation x@(IAutoApp _ _ _) = pure x
taskInvocation x@(IWithApp _ _ _) = pure x
taskInvocation x@(IVar _ _) = pure x
taskInvocation x = failAt (getFC x) "Failed to extract invocation from lambda"

||| Extract a task's inner typename
taskTName : TTImp -> Elab Name
taskTName (IVar _ n) = pure n
taskTName (IApp _ f _) = taskTName f
taskTName (INamedApp _ f _ _) = taskTName f
taskTName (IAutoApp _ f _) = taskTName f
taskTName (IWithApp _ f _) = taskTName f
taskTName t = failAt (getFC t) "Couldn't get type name"

||| Extract the lambda's arguments as a list
freeVarsLambda : TTImp -> List (Name, TTImp)
freeVarsLambda (ILam _ _ _ (Just n) a r) = (n, a) :: freeVarsLambda r
freeVarsLambda (ILam _ _ _ Nothing _ r) = freeVarsLambda r
freeVarsLambda _ = []

record ConInfo where
  constructor MkConInfo
  name : Name
  sig : TTImp

%runElab derive "ConInfo" [Show]

record TypeInfo where
  constructor MkTypeInfo
  name : Name
  sig : TTImp
  cons : List ConInfo

%runElab derive "TypeInfo" [Show]

record Task where
  constructor MkTask
  taskQuote : TTImp
  taskType : TTImp
  typeName : Name
  outputName : Name
  type : Monomorphisation2.TypeInfo

record TaskState where
  constructor MkTaskState
  unis : List $ Either UnificationError UnificationResult

TaskOp : (Type -> Type) -> Type
TaskOp m = (Monad m, MonadReader Task m)

ConOp : (Type -> Type) -> Type
ConOp m = (Monad m, MonadReader Task m, MonadReader ConInfo m)

UniConOp : (Type -> Type) -> Type
UniConOp m = (Monad m, MonadReader Task m, MonadReader ConInfo m, MonadReader UnificationResult m)

convertCon : Con na va -> Elab ConInfo
convertCon con = do
  (name, sig) <- lookupName con.name
  pure $ MkConInfo { name
                   , sig
                   }

getTypeConstructors : Name -> Elab $ List ConInfo
getTypeConstructors typeName = do
  typeInfo <- Types.getInfo' typeName
  traverse convertCon typeInfo.cons

getTask : TypeTask l => l -> Name -> Elab Task
getTask l' outputName = do
  taskQuote <- quote l'
  taskType <- quote l
  invocation <- taskInvocation taskQuote
  typeName <- taskTName invocation
  cons <- getTypeConstructors typeName
  let taskTypeInfo = MkTypeInfo { name = typeName
                                , sig = taskType
                                , cons
                                }

  pure $ MkTask { taskQuote
                , taskType
                , typeName
                , outputName
                , type = taskTypeInfo
                }

mapCons : Monad m =>
          (f : Task -> ConInfo -> m t) -> 
          Task -> 
          m $ List t
mapCons f task = traverse (f task) task.type.cons

mapCons_ : Monad m =>
          (f : Task -> ConInfo -> m t) -> 
          Task -> 
          m ()
mapCons_ f task = mapCons f task *> pure ()

mapUConsM : Monad m =>
            (f : Task -> ConInfo -> Either UnificationError UnificationResult -> m t) ->
            Task ->
            TaskState ->
            m $ List t
mapUConsM f task state =
  traverse (\(x, y) => f task x y) $ zip task.type.cons state.unis

mapUConsM_ : Monad m =>
            (f : Task -> ConInfo -> Either UnificationError UnificationResult -> m t) ->
            Task ->
            TaskState ->
            m ()
mapUConsM_ f task state = mapUConsM f task state *> pure ()

mapUCons : Monad m =>
           (f : Task -> ConInfo -> UnificationResult -> m t) ->
           Task ->
           TaskState ->
           m $ List t
mapUCons f task state = traverseA (\(x, y) => f task x y) $ zip task.type.cons state.unis
  where
    traverseA : ((ConInfo, UnificationResult) -> m t) -> List (ConInfo, Either UnificationError UnificationResult) -> m $ List t
    traverseA _ [] = pure []
    traverseA f ((ci, Left _) :: xs) = traverseA f xs
    traverseA f ((ci, Right ui) :: xs) = pure $ !(f (ci, ui)) :: !(traverseA f xs)

mapUCons_ : Monad m =>
            (f : Task -> ConInfo -> UnificationResult -> m t) ->
            Task ->
            TaskState ->
            m ()
mapUCons_ f task taskState = mapUCons f task taskState *> pure ()

arg2tup : Arg -> (Name, TTImp)
arg2tup (MkArg count piInfo Nothing type) = (?nameImpossible, type)
arg2tup (MkArg count piInfo (Just x) type) = (x, type)

unifyCon : Elaboration m =>
           Task -> ConInfo ->
           m $ Either UnificationError UnificationResult
unifyCon task ci = do
  let (targs, tret) = unPi task.taskType
  let (cargs, cret) = unPi ci.sig
  inv <- taskInvocation task.taskQuote
  doUnification (freeVarsLambda task.taskQuote)
                inv (map arg2tup cargs) cret

assembleApp : List Arg -> TTImp -> TTImp
assembleApp [] x = x
assembleApp ((MkArg count ImplicitArg name type) :: xs) y
  = assembleApp xs $ INamedApp EmptyFC y (fromMaybe ?impp name) $ IVar EmptyFC $ fromMaybe ?imp name
assembleApp ((MkArg count ExplicitArg name type) :: xs) y
  = assembleApp xs $ IApp EmptyFC y $ IVar EmptyFC $ fromMaybe ?imp1 name
assembleApp ((MkArg count AutoImplicit name type) :: xs) y
  = assembleApp xs $ IAutoApp EmptyFC y $ IVar EmptyFC $ fromMaybe ?imp2 name
assembleApp ((MkArg count (DefImplicit x) name type) :: xs) y
  = assembleApp xs $ INamedApp EmptyFC y (fromMaybe ?imp3 name) $ IVar EmptyFC $ fromMaybe ?imp4 name

amendCArgs : List Arg -> SortedMap Name TTImp -> SortedMap Name TTImp -> List Arg
amendCArgs [] _ _ = []
amendCArgs ((MkArg count piInfo Nothing type) :: xs) rhsS acting
  = MkArg count piInfo Nothing (substituteVariables acting type) :: amendCArgs xs rhsS acting
amendCArgs ((MkArg count piInfo (Just x) type) :: xs) rhsS acting with (lookup x rhsS)
  amendCArgs ((MkArg count piInfo (Just x) type) :: xs) rhsS acting | Nothing
    = MkArg count piInfo (Just x) (substituteVariables acting type) :: amendCArgs xs rhsS acting
  amendCArgs ((MkArg count piInfo (Just x) type) :: xs) rhsS acting | Just tv
    = amendCArgs xs rhsS (insert x tv acting)

mkMonoConInfo : Monad m =>
                Task -> ConInfo ->
                UnificationResult ->
                m ConInfo
mkMonoConInfo task ci cu = do
  let (targs, _) = unPi task.taskType
  let (cargs, cret) = unPi ci.sig
  let retTy' = assembleApp targs $ IVar EmptyFC task.outputName
  let retTy = substituteVariables cu.lhsVars retTy'
  let amended = amendCArgs cargs cu.rhsVarsEO empty
  pure $ MkConInfo (dropNS ci.name) $ piAll retTy amended

mkMonoTy : Monad m =>
           Task -> TaskState ->
           m Monomorphisation2.TypeInfo
mkMonoTy task state = do
  cons <- mapUCons mkMonoConInfo task state
  pure $ MkTypeInfo task.outputName task.taskType cons

(.ity) : ConInfo -> ITy
(.ity) ci = mkTy (dropNS ci.name) ci.sig

(.decl) : Monomorphisation2.TypeInfo -> Decl
(.decl) ti = iData Public ti.name ti.sig [] $ map (.ity) ti.cons

||| Emit all the necessary information
monoEmit : Elaboration m =>
           Task -> TaskState -> m ()
monoEmit task state = do
  logMsg "monomorphiser" 0 "Unifieds: \{show state.unis}"
  ty <- mkMonoTy task state
  logMsg "monomorphiser" 0 "Generated type: \{show ty}"
  let tydecl = ty.decl
  logMsg "monomorphiser" 0 "Generated decl: \{show tydecl}"
  let nsname : String = show task.outputName
  declare $ [INamespace EmptyFC (MkNS [nsname]) [tydecl]]
  pure ()

||| Unify constructors
monoTask : Elaboration m => Task -> m ()
monoTask task = do
  uni_res <- mapCons unifyCon task
  let state = MkTaskState uni_res
  monoEmit task state

||| Monomorphise a type based on a lambda and a name
public export
monomorphise : TypeTask l => l -> Name -> Elab ()
monomorphise l outputName = do
  task <- getTask l outputName
  monoTask task

%macro
public export
monomorphise' : TypeTask l => l -> Name -> Elab ()
monomorphise' = monomorphise
