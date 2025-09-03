module Language.Reflection.Unification3

import public Language.Reflection.Unification3.Context
import public Language.Reflection.Unification3.Error
import public Language.Reflection.Unification3.IR
import public Language.Reflection.Unification3.IR.AppChain
import public Language.Reflection.Unification3.Solver
import public Language.Reflection.Unification3.Log

import public Control.Monad.Error.Either
import public Control.Monad.Error.Interface
import public Control.Monad.State

import public Decidable.Equality

import public Language.Reflection
import public Language.Reflection.TT
import public Language.Reflection.TTImp
import public Language.Reflection.Syntax

import public Data.Fin
import public Data.Nat
import public Data.Vect
import public Data.SortedMap

public export
typeofConst : Constant -> IRTerm fvs bjn
typeofConst (I i) = IRGlobalVar "Int"
typeofConst (BI i) = IRGlobalVar "Integer"
typeofConst (I8 i) = IRGlobalVar "Int8"
typeofConst (I16 i) = IRGlobalVar "Int16"
typeofConst (I32 i) = IRGlobalVar "Int32"
typeofConst (I64 i) = IRGlobalVar "Int64"
typeofConst (B8 m) = IRGlobalVar "Bits8"
typeofConst (B16 m) = IRGlobalVar "Bits16"
typeofConst (B32 m) = IRGlobalVar "Bits32"
typeofConst (B64 m) = IRGlobalVar "Bits64"
typeofConst (Str str) = IRGlobalVar "String"
typeofConst (Ch c) = IRGlobalVar "Char"
typeofConst (Db dbl) = IRGlobalVar "Double"
typeofConst (PrT pty) = IRGlobalVar "PrimType"
typeofConst WorldVal = IRType

parameters 
  {auto _ : Monad m}
  {auto _ : MonadError UnificationError m}
  {auto _ : MonadLog m}
  (gv : GlobalVars)
  {bds : Bounds}
  (afv : AllFreeVars bds)

  public export
  unify : MonadState (Constraints bds) m =>
          (isLeft : Bool) ->
          {bjn : Nat} ->
          (bv : bvsT isLeft bds bjn) ->
          (t : term isLeft bds bjn) ->
          (isLeft' : Bool) ->
          {bjn' : Nat} ->
          (bv : bvsT isLeft' bds bjn') ->
          (t' : term isLeft' bds bjn') ->
          m ()

  public export
  unifyAppChains : MonadState (Constraints bds) m =>
          (isLeft : Bool) ->
          {bjn : Nat} ->
          (bv : bvsT isLeft bds bjn) ->
          (t : appChain isLeft bds bjn) ->
          (isLeft' : Bool) ->
          {bjn' : Nat} ->
          (bv : bvsT isLeft' bds bjn') ->
          (t' : appChain isLeft' bds bjn') ->
          m ()

  public export
  fvEqFv : MonadState (Constraints bds) m =>
           (isLeft : Bool) ->
           (l : Fin (thisFvs isLeft bds)) ->
           (isLeft' : Bool) ->
           (r : Fin (thisFvs isLeft' bds)) ->
           m ()

  public export
  fvEqExpr : MonadState (Constraints bds) m =>
             (isLeft : Bool) ->
             (l : Fin (thisFvs isLeft bds)) ->
             (isLeft' : Bool) ->
             (r : term isLeft' bds bjn') ->
             m ()

  public export
  ford : MonadState (Constraints bds) m =>
         (isLeft : Bool) ->
         (l : term isLeft bds bjn) ->
         (isLeft' : Bool) ->
         (r : term isLeft' bds bjn') ->
         m ()

  parameters 
    (isLeft : Bool)
    {auto st : MonadState (Constraints bds) m}
    parameters
      {bjn : Nat}
      (bv : bvsT isLeft bds bjn)

      public export
      typeof : term isLeft bds bjn -> m $ term isLeft bds bjn

      public export
      typeofAppChain : appChain isLeft bds bjn -> m $ term isLeft bds bjn

      public export
      typeofPiAppChain : appChain isLeft bds bjn -> m $ term isLeft bds bjn

      public export
      reduce : term isLeft bds bjn -> m $ term isLeft bds bjn

      public export
      reduceAppChain : appChain isLeft bds bjn -> m $ term isLeft bds bjn 

      public export
      typecheck : term isLeft bds bjn -> term isLeft bds bjn -> m ()
      typecheck val type = do
        logStr 10 "typecheck \{show isLeft} \{show val} \{show type}"
        valT <- typeof val
        unify isLeft bv valT isLeft bv type
    
    typeof bv t = do
      logStr 10 "typeof \{show isLeft} \{show t}"
      case t of
        IRFreeVar x => pure $ raise bjn $ snd $ index x $ thisFv isLeft bds afv
        IRLocalVar x => pure $ snd $ index x bv
        IRGlobalVar nm =>
          case lookup nm gv of
            Just (t, _) => pure $ setFV $ raise bjn t
            Nothing => throwError $ GlobalVarNotFound nm
        IRType => pure IRType
        t@(IRApp x y) => typeofAppChain isLeft bv $ mkAC t
        t@(IRAutoApp x y) => typeofAppChain isLeft bv $ mkAC t
        t@(IRNamedApp x nm y) => typeofAppChain isLeft bv $ mkAC t
        IRLam rig pinfo nm x y =>
          IRPi rig pinfo nm x <$> typeof isLeft (bv :< (nm, x)) y
        IRPi rig pinfo nm x y => pure IRType
        IRLet rig nm type val body => do
          valT <- typeof isLeft bv val
          unify isLeft bv valT isLeft bv type
          typeof isLeft bv $ subst' val 0 body
        IRPrim c => pure $ typeofConst c

    reduce bv t = do
      logStr 10 "reduce \{show isLeft} \{show t}"
      case t of
        IRFreeVar x => pure $ IRFreeVar x
        IRLocalVar x => pure $ IRLocalVar x
        IRGlobalVar nm => pure $ IRGlobalVar nm
        IRType => pure $ IRType
        t@(IRApp x y) => reduceAppChain isLeft bv $ mkAC t
        t@(IRAutoApp x y) => reduceAppChain isLeft bv $ mkAC t
        t@(IRNamedApp x nm y) => reduceAppChain isLeft bv $ mkAC t
        IRLam rig pinfo nm x y => do
          IRLam rig
            <$> traverse (\n => reduce isLeft bv n) pinfo
            <*> pure nm
            <*> reduce isLeft bv x
            <*> reduce isLeft (bv :< (nm, x)) y 
        IRPi rig pinfo nm x y => do
          IRPi rig
            <$> traverse (\n => reduce isLeft bv n) pinfo
            <*> pure nm
            <*> reduce isLeft bv x
            <*> reduce isLeft (bv :< (nm, x)) y 
        IRLet rig nm type val body => do
          typecheck isLeft bv val type
          reduce isLeft bv $ subst' val 0 body
        IRPrim c => pure $ IRPrim c

    typeofAppChain bv ac = do
      logStr 10 $ concat {t = List}
        [ "typeofAppChain \{show isLeft} lhs=\{show ac.lhs}"
        , "args=\{show $ ac.args} nameds = \{show $ ac.nameds}"
        ]
      if ac.argCount == 0 
         then typeof isLeft bv ac.lhs 
         else case ac.lhs of
          IRLam rig pinfo nm ty body => do
            let Just (arg, ac) = nextArg pinfo nm ac
            | Nothing => throwError $ AppNameNotFoundError nm
            typecheck isLeft bv arg ty
            typeofAppChain isLeft bv $ 
              {lhs := subst' arg 0 body} ac
          IRGlobalVar _ => do
            typeof_lhs <- typeof bv ac.lhs
            typeofPiAppChain bv $ {lhs := typeof_lhs} ac
          IRFreeVar _ => do
            typeof_lhs <- typeof bv ac.lhs
            typeofPiAppChain bv $ {lhs := typeof_lhs} ac
          IRLocalVar _ => do
            typeof_lhs <- typeof bv ac.lhs
            typeofPiAppChain bv $ {lhs := typeof_lhs} ac
          _ => throwError AppBadLhsError

    typeofPiAppChain bv ac = do
      logStr 10 $ concat {t = List} $
        [ "typeofPiAppChain \{show isLeft} lhs=\{show ac.lhs} "
        , "args=\{show $ ac.args} nameds = \{show $ ac.nameds}"
        ]
      if ac.argCount == 0 
         then pure ac.lhs 
         else case ac.lhs of
          IRPi rig pinfo nm ty body => do
            let Just (arg, ac) = nextArg pinfo nm ac
            | Nothing => throwError $ AppNameNotFoundError nm
            typecheck isLeft bv arg ty
            typeofPiAppChain isLeft bv $ 
              {lhs := subst' arg 0 body} ac
          IRGlobalVar _ => do
            pure $ unAC ac
          IRLocalVar _ => do
            pure $ unAC ac
          IRFreeVar _ => do
            pure $ unAC ac
          _ => throwError AppBadLhsError

    reduceAppChain bv ac = do
      logStr 10 $ concat {t = List}
        [ "reduceAppChain \{show isLeft} lhs=\{show ac.lhs} "
        , "args=\{show $ ac.args}  nameds = \{show $ ac.nameds}"
        ]
      if ac.argCount == 0
        then reduce isLeft bv ac.lhs
        else case ac.lhs of
          IRLam rig pinfo nm ty body => do
            let Just (arg, ac) = nextArg pinfo nm ac
            | Nothing => throwError $ AppNameNotFoundError nm
            typecheck isLeft bv arg ty
            reduceAppChain isLeft bv $ 
              {lhs := subst' arg 0 body} ac
          IRGlobalVar _ => pure $ unAC ac
          IRFreeVar _ => pure $ unAC ac
          IRLocalVar _ => pure $ unAC ac
          _ => throwError AppBadLhsError

  fvEqFv isLeft fv isLeft' fv' = do
    logStr 10 "fvEqFv \{show isLeft} \{show fv} \{show isLeft'} \{show fv'}"
    cs <- get
    let bi1 = bIndexOf isLeft fv cs
    let bi2 = bIndexOf isLeft' fv' cs
    let b1 = index bi1 cs.bucketData
    let b2 = index bi2 cs.bucketData
    case (b1.equalsTo, b2.equalsTo) of
      (Just e1@(it1 ** v1), Just e2@(it2 ** v2)) => do
        let nmL = merge b1.membersL b2.membersL
        let nmR = merge b1.membersR b2.membersR
        unify it1 [<] v1 it2 [<] v2
        put $ 
          mergeIntoAndUpdate cs bi1 bi2 (toList nmL) (toList nmR) $ 
            {membersL := nmL, membersR := nmR} b1
      (m1, m2) => do
        let nmL = merge b1.membersL b2.membersL
        let nmR = merge b1.membersR b2.membersR
        put $ 
          mergeIntoAndUpdate cs bi1 bi2 (toList nmL) (toList nmR) $ 
            {membersL := nmL, membersR := nmR, equalsTo := m1 <|> m2} b1
 
  fvEqExpr isLeft fv isLeft' expr = do
    logStr 10 "fvEqExpr \{show isLeft} \{show fv} \{show isLeft'} \{show expr}"
    b <- gets $ bucketOf isLeft fv
    let (Just unbound) = unbind expr
    | _ => throwError UnhandledFvEqBvError
    case b.equalsTo of
      Nothing => 
        modify $ 
          setBucketOf isLeft fv $ 
            {equalsTo := Just (isLeft' ** unbound)} b
      Just (isLeft'' ** oldVal) => do
        logStr 11 "old val of \{show fv} is \{show oldVal}"
        unify isLeft' [<] unbound isLeft'' [<] oldVal

  ford isLeft t isLeft' t' = do
    logStr 10 "ford \{show isLeft} \{show t} \{show isLeft'} \{show t'}"
    let (Just ub, Just ub') = (unbind t, unbind t')
    | _ => throwError UnhandledFvEqBvError
    modify $ {fords $= (((isLeft ** ub), (isLeft' ** ub')) ::)}

  unifyAppChains isLeft bv ac isLeft' bv' ac' = do
    logStr 10 $ concat {t = List}
      [ "unifyAppChains \{show isLeft} \{show ac.lhs} "
      , "\{show ac.args} \{show isLeft'} \{show ac'.lhs} \{show ac'.args}"
      ]
    let True = length ac.args == length ac'.args 
            && length ac.autos == length ac'.autos 
            && length ac.explicits == length ac'.explicits
    | _ => throwError $ AppUnificationError
    unify isLeft bv ac.lhs isLeft' bv' ac'.lhs
    traverse_ 
      (\(a, b) => 
        unify 
          isLeft bv (index a ac.args).arg 
          isLeft' bv' (index b ac'.args).arg) $ 
            zip ac.autos ac'.autos
    traverse_ 
      (\(a, b) => 
        unify 
          isLeft bv (index a ac.args).arg 
          isLeft' bv' (index b ac'.args).arg) $ 
            zip ac.explicits ac'.explicits
    let nll = zip (kvList ac.nameds) (kvList ac'.nameds)
    traverse_ 
      (\((n1, a), (n2, b)) => 
        if n1 == n2 
           then 
            unify isLeft bv (index a ac.args).arg 
                  isLeft' bv' (index b ac'.args).arg 
           else throwError AppUnificationError) 
      nll

  unify isLeft bv t isLeft' bv' t' = do
    logStr 10 "unify \{show isLeft} \{show t} \{show isLeft'} \{show t'}"
    rt <- reduce isLeft bv t
    rt' <- reduce isLeft' bv' t'
    if (t /= rt || t' /= rt')
       then unify isLeft bv rt isLeft' bv' rt'
       else case (t, t') of
      (IRGlobalVar nm, IRGlobalVar nm') =>  -- TODO: Actual name resolution!
        if dropNS nm == dropNS nm' 
           then pure () 
           else throwError $ NEVarsError nm nm'
      (IRLocalVar y, IRLocalVar y') => do
        let (Yes p, Yes p') = (decEq isLeft isLeft', decEq bjn bjn')
        | _ => do
           let (bn, _) = index y bv
           let (bn', _) = index y' bv'
           throwError $ NEVarsError bn bn'
        let True = bv == rewrite p' in rewrite p in bv'
        | _ => do
           let (bn, _) = index y bv
           let (bn', _) = index y' bv'
           throwError $ NEVarsError bn bn'
        if y == (rewrite p' in y') then pure () else do
           let (bn, _) = index y bv
           let (bn', _) = index y' bv'
           throwError $ NEVarsError bn bn'
      (IRFreeVar f, IRFreeVar f') => fvEqFv isLeft f isLeft' f'
      (IRFreeVar f, IRLocalVar b') => do
        let (n1, _) = index f $ thisFv isLeft bds afv
        let (n2, _) = index b' bv'
        throwError $ NEVarsError n1 n2
      (IRLocalVar b, IRFreeVar f') => do
        let (n1, _) = index b bv
        let (n2, _) = index f' $ thisFv isLeft' bds afv
        throwError $ NEVarsError n1 n2
      (IRFreeVar f, e') => fvEqExpr isLeft f isLeft' e'
      (e, IRFreeVar f') => fvEqExpr isLeft' f' isLeft e
      (IRLocalVar y, _) => throwError UnifyingLocalVarError
      (_, IRLocalVar y') => throwError UnifyingLocalVarError
      (l@(IRApp _ _), r) => unifyAppChains isLeft bv (mkAC l) isLeft' bv' (mkAC r) 
      (l@(IRAutoApp _ _), r) => unifyAppChains isLeft bv (mkAC l) isLeft' bv' (mkAC r) 
      (l@(IRNamedApp _ _ _), r) => unifyAppChains isLeft bv (mkAC l) isLeft' bv' (mkAC r) 
      (l, r@(IRApp _ _)) => unifyAppChains isLeft bv (mkAC l) isLeft' bv' (mkAC r) 
      (l, r@(IRAutoApp _ _)) => unifyAppChains isLeft bv (mkAC l) isLeft' bv' (mkAC r) 
      (l, r@(IRNamedApp _ _ _)) => unifyAppChains isLeft bv (mkAC l) isLeft' bv' (mkAC r) 
      (IRPi rig pinfo nm ty body, IRPi rig' pinfo' nm' ty' body') => do
        let True = rig == rig'
        | _ => throwError PiUnificationError
        -- TODO: compare pinfos
        unify isLeft bv ty isLeft' bv' ty'
        unify isLeft (bv :< (nm, ty)) body isLeft' (bv' :< (nm', ty')) body'
      (IRLam rig pinfo nm ty body, IRLam rig' pinfo' nm' ty' body') => do
        let True = rig == rig'
        | _ => throwError LamUnificationError
        -- TODO: compare pinfos
        unify isLeft bv ty isLeft' bv' ty'
        unify isLeft (bv :< (nm, ty)) body isLeft' (bv' :< (nm', ty')) body'
      (IRPrim c, IRPrim c') => 
        if c == c' then pure () else throwError $ NEPrimitivesError c c' 
      (IRType, IRType) => pure ()
      (_, _) => throwError UnsupportedUnificationError
