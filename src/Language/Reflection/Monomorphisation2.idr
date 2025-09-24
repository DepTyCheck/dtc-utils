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
import public Language.Reflection.Unifier.LegacyUnifier
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
taskTName : Elaboration m => TTImp -> m Name
taskTName (IVar _ n) = pure n
taskTName (IApp _ f _) = taskTName f
taskTName (INamedApp _ f _ _) = taskTName f
taskTName (IAutoApp _ f _) = taskTName f
taskTName (IWithApp _ f _) = taskTName f
taskTName t = failAt (getFC t) "Couldn't get type name"


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
  fullInvocation : TTImp
  type : Monomorphisation2.TypeInfo

record TaskState where
  constructor MkTaskState
  unis : List $ Either UnificationError UnificationResult

convertCon : Elaboration m => Con na va -> m ConInfo
convertCon con = do
  (name, sig) <- lookupName con.name
  pure $ MkConInfo { name
                   , sig
                   }

getTypeConstructors : Elaboration m => Name -> m $ List ConInfo
getTypeConstructors typeName = do
  typeInfo <- Types.getInfo' typeName
  traverse convertCon typeInfo.cons

getTask : TypeTask l => l -> Name -> Elab Task
getTask l' outputName = do
  taskQuote <- quote l'
  taskType <- quote l
  fullInvocation <- taskInvocation taskQuote
  typeName <- taskTName fullInvocation
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
                , fullInvocation
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
  let (targs, tret) = unLambda task.taskQuote
  let (cargs, cret) = unPi ci.sig
  let inv = task.fullInvocation
  doUnification (map arg2tup targs)
                inv (map arg2tup cargs) cret

args2App : List Arg -> TTImp -> TTImp
args2App [] x = x
args2App ((MkArg count ImplicitArg name type) :: xs) y
  = args2App xs $ INamedApp EmptyFC y (fromMaybe ?impp name) $ IVar EmptyFC $ fromMaybe ?imp name
args2App ((MkArg count ExplicitArg name type) :: xs) y
  = args2App xs $ IApp EmptyFC y $ IVar EmptyFC $ fromMaybe ?imp1 name
args2App ((MkArg count AutoImplicit name type) :: xs) y
  = args2App xs $ IAutoApp EmptyFC y $ IVar EmptyFC $ fromMaybe ?imp2 name
args2App ((MkArg count (DefImplicit x) name type) :: xs) y
  = args2App xs $ INamedApp EmptyFC y (fromMaybe ?imp3 name) $ IVar EmptyFC $ fromMaybe ?imp4 name

(.outputInvocation) : Task -> TTImp
(.outputInvocation) task = do
  let (targs, _) = unPi task.taskType
  args2App targs $ IVar EmptyFC task.outputName

substituteInArgs : List Arg -> SortedMap Name TTImp -> SortedMap Name TTImp -> List Arg
substituteInArgs [] _ _ = []
substituteInArgs ((MkArg count piInfo Nothing type) :: xs) rhsS acting
  = MkArg count piInfo Nothing (substituteVariables acting type) :: substituteInArgs xs rhsS acting
substituteInArgs ((MkArg count piInfo (Just x) type) :: xs) rhsS acting with (lookup x rhsS)
  substituteInArgs ((MkArg count piInfo (Just x) type) :: xs) rhsS acting | Nothing
    = MkArg count piInfo (Just x) (substituteVariables acting type) :: substituteInArgs xs rhsS acting
  substituteInArgs ((MkArg count piInfo (Just x) type) :: xs) rhsS acting | Just tv
    = substituteInArgs xs rhsS (insert x tv acting)

mkMonoConInfo : Monad m =>
                Task -> ConInfo ->
                UnificationResult ->
                m ConInfo
mkMonoConInfo task ci cu = do
  let (targs, _) = unPi task.taskType
  let (cargs, _) = unPi ci.sig
  let retTy = substituteVariables cu.lhsVars task.outputInvocation
  let amended = substituteInArgs cargs cu.rhsVarsEO empty
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

||| Substitute IPis' return type and set all arguments to implicit
rewireIPiImplicit : TTImp -> TTImp -> TTImp
rewireIPiImplicit (IPi fc count pinfo mn arg ret) y = IPi fc count ImplicitArg mn arg $ rewireIPiImplicit ret y
rewireIPiImplicit x y = y

||| Generate IPi with implicit type arguments and given return
genericSig : Task -> TTImp -> TTImp
genericSig task = rewireIPiImplicit task.taskType

(.fullInvocation) : ConInfo -> TTImp
(.fullInvocation) ci = args2App (fst $ unPi ci.sig) $ IVar EmptyFC ci.name

mToPClause : Monad m => Task -> ConInfo -> UnificationResult -> m Clause
mToPClause task ci uniRes = do
  pure $ PatClause EmptyFC `(m2p_impl ~(ci.fullInvocation)) task.fullInvocation

mToPDecls : Elaboration m =>
             Task -> TaskState -> m $ List Decl
mToPDecls task state = do
  let sig = genericSig task `(~(task.outputInvocation) -> ~(task.fullInvocation))
  clauses <- mapUCons mToPClause task state
  pure [ IClaim $ NoFC $ MkIClaimData MW Public [] $ MkTy EmptyFC (NoFC "m2p_impl") sig
       , IDef EmptyFC "m2p_impl" clauses
       ]

pToMClause : Monad m => Task -> ConInfo -> UnificationResult -> m Clause
pToMClause task ci uniRes = do
  pure $ PatClause EmptyFC `(m2p_impl ~(task.fullInvocation)) ci.fullInvocation

pToMDecls : Elaboration m =>
             Task -> TaskState -> m $ List Decl
pToMDecls task state = do
  let sig = genericSig task `(~(task.fullInvocation) -> ~(task.outputInvocation) )
  clauses <- mapUCons mToPClause task state
  pure [ IClaim $ NoFC $ MkIClaimData MW Public [] $ MkTy EmptyFC (NoFC "p2m_impl") sig
       , IDef EmptyFC "p2m_impl" clauses
       ]

||| Monomorphise a type based on a lambda and a name
public export
monomorphise : TypeTask l => l -> Name -> Elab ()
monomorphise l outputName = do
  task <- getTask l outputName
  uni_res <- mapCons unifyCon task
  let state = MkTaskState uni_res
  logMsg "monomorphiser" 0 "Unifieds: \{show state.unis}"
  ty <- mkMonoTy task state
  logMsg "monomorphiser" 0 "Generated type: \{show ty}"
  let tydecl = ty.decl
  logMsg "monomorphiser" 0 "Generated decl: \{show tydecl}"
  let nsname : String = show task.outputName
  toPoly <- mToPDecls task state
  logMsg "monomorphiser" 0 "ToPoly: \{show toPoly}"

%macro
public export
monomorphise' : TypeTask l => l -> Name -> Elab ()
monomorphise' = monomorphise
