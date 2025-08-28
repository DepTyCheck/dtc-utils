module Language.Reflection.Unification3.IR.AppChain

import public Language.Reflection.Unification3.IR

import public Data.SortedMap

public export
data IRAppType = IRExplicit | IRAutoImplicit | IRNamed Name

public export
Show IRAppType where
  show IRExplicit = "IRExplicit"
  show IRAutoImplicit = "IRAutoImplicit"
  show (IRNamed nm) = "IRNamed \{show nm}"

public export
record IRAppArg (fvs : Nat) (bjn : Nat) where
  constructor MkAA
  argTy : IRAppType
  arg : IRTerm fvs bjn

public export
Show (IRAppArg fvs bjn) where
  show (MkAA argTy arg) = "MkAA \{show argTy} \{show arg}"

public export
appArg : IRTerm fvs bjn -> IRAppArg fvs bjn -> IRTerm fvs bjn
appArg l (MkAA IRExplicit arg) = IRApp l arg
appArg l (MkAA IRAutoImplicit arg) = IRAutoApp l arg
appArg l (MkAA (IRNamed nm) arg) = IRNamedApp l nm arg

public export
peelAppTelescope : IRTerm fvs bjn -> (IRTerm fvs bjn, List $ IRAppArg fvs bjn)
peelAppTelescope t = go t []
  where
  go : IRTerm fvs bjn -> 
       List (IRAppArg fvs bjn) -> 
       (IRTerm fvs bjn, List $ IRAppArg fvs bjn)
  go (IRApp l r) rest = go l $ MkAA IRExplicit r :: rest
  go (IRAutoApp l r) rest = go l $ MkAA IRAutoImplicit r :: rest
  go (IRNamedApp l nm r) rest = go l $ MkAA (IRNamed nm) r :: rest
  go t rest = (t, rest)

public export
applyAppTelescope : IRTerm fvs bjn -> List (IRAppArg fvs bjn) -> IRTerm fvs bjn
applyAppTelescope = foldl appArg

public export
record AppChain (fvs : Nat) (bjn : Nat) where
  constructor MkAC
  lhs : IRTerm fvs bjn
  argCount : Nat
  args : Vect argCount (IRAppArg fvs bjn)
  explicits : List (Fin argCount)
  autos : List (Fin argCount)
  nameds : SortedMap Name (Fin argCount)

public export
deleteIndex : (i : Fin (S n)) -> (j : Fin (S n)) -> (i == j) = False => Fin n
deleteIndex FZ (FS x) = x
deleteIndex (FS FZ) FZ = FZ
deleteIndex (FS (FS x)) FZ = FZ
deleteIndex (FS FZ) (FS y) = FS $ deleteIndex FZ y
deleteIndex (FS (FS x)) (FS y) = FS $ deleteIndex (FS x) y

public export
mapDI : Fin (S n) -> List (Fin (S n)) -> List (Fin n)
mapDI a [] = []
mapDI a (x :: xs) with (a == x) proof p
  mapDI a (x :: xs) | True = mapDI a xs
  mapDI a (x :: xs) | False = deleteIndex a x :: mapDI a xs

public export
mapDIMap : Fin (S n) -> SortedMap Name (Fin (S n)) -> SortedMap Name (Fin n)
mapDIMap a sm = do
  let (lk, lv) = unzip $ toList sm
  fromList $ zip lk $ mapDI a lv

public export
nextExplicit : AppChain fvs bjn -> Maybe (IRTerm fvs bjn, AppChain fvs bjn)
nextExplicit ac with (ac.argCount) proof p
  nextExplicit ac | Z = Nothing
  nextExplicit ac | S n = do
    case ac.explicits of
      [] => Nothing
      (x :: xs) => Just $ do
        let x' = rewrite sym p in x
        let ret1 = arg $ index x ac.args
        let aa = replace {p = \x => Vect x (IRAppArg fvs bjn)} p ac.args
        let aex = replace {p = \x => List (Fin x)} p ac.explicits
        let aauto = replace {p = \x => List (Fin x)} p ac.autos
        let anam = replace {p = \x => SortedMap Name (Fin x)} p ac.nameds
        let da = deleteAt {len = n} x' aa
        let maex = mapDI x' aex
        (ret1
        , MkAC ac.lhs n da (mapDI x' aex) (mapDI x' aauto) (mapDIMap x' anam))

public export
nextAuto : AppChain fvs bjn -> Maybe (IRTerm fvs bjn, AppChain fvs bjn)
nextAuto ac with (ac.argCount) proof p
  nextAuto ac | Z = Nothing
  nextAuto ac | S n = do
    case ac.autos of
      [] => Nothing
      (x :: xs) => Just $ do
        let x' = rewrite sym p in x
        let ret1 = arg $ index x ac.args
        let aa = replace {p = \x => Vect x (IRAppArg fvs bjn)} p ac.args
        let aex = replace {p = \x => List (Fin x)} p ac.explicits
        let aauto = replace {p = \x => List (Fin x)} p ac.autos
        let anam = replace {p = \x => SortedMap Name (Fin x)} p ac.nameds
        let da = deleteAt {len = n} x' aa
        let maex = mapDI x' aex
        (ret1
        , MkAC ac.lhs n da (mapDI x' aex) (mapDI x' aauto) (mapDIMap x' anam))

public export
nextNamed : Name -> AppChain fvs bjn -> Maybe (IRTerm fvs bjn, AppChain fvs bjn)
nextNamed nm ac with (ac.argCount) proof p
  nextNamed nm ac | Z = Nothing
  nextNamed nm ac | S n = do
    x <- lookup nm ac.nameds
    let x' = rewrite sym p in x
    let ret1 = arg $ index x ac.args
    let aa = replace {p = \x => Vect x (IRAppArg fvs bjn)} p ac.args
    let aex = replace {p = \x => List (Fin x)} p ac.explicits
    let aauto = replace {p = \x => List (Fin x)} p ac.autos
    let anam = replace {p = \x => SortedMap Name (Fin x)} p ac.nameds
    let da = deleteAt {len = n} x' aa
    Just (ret1
    , MkAC ac.lhs n da (mapDI x' aex) (mapDI x' aauto) (mapDIMap x' (delete nm anam)))

public export
nextArg : PiInfo (IRTerm fvs bjn) -> Name -> AppChain fvs bjn -> Maybe (IRTerm fvs bjn, AppChain fvs bjn)
nextArg ImplicitArg nm ac = nextNamed nm ac
nextArg ExplicitArg nm ac = nextExplicit ac <|> nextNamed nm ac
nextArg AutoImplicit nm ac = nextAuto ac <|> nextNamed nm ac
nextArg (DefImplicit x) nm ac = pure $ fromMaybe (x, ac) $ nextNamed nm ac

record AppChain' (fvs : Nat) (bjn : Nat) (n : Nat) where
  constructor MkAC'
  autos : SnocList (Fin n)
  explicits : SnocList (Fin n)
  nameds : SortedMap Name (Fin n)

acfold : AppChain' fvs bjn l -> (Fin l, IRAppArg fvs bjn) -> AppChain' fvs bjn l
acfold ac (idx, MkAA IRExplicit arg) = {explicits $= (:< idx)} ac
acfold ac (idx, MkAA IRAutoImplicit arg) = {autos $= (:< idx)} ac
acfold ac (idx, MkAA (IRNamed nm) arg) = {nameds $= insert nm idx} ac

toAC : {fvs : Nat} -> {bjn : Nat} -> (IRTerm fvs bjn, List $ IRAppArg fvs bjn) -> AppChain fvs bjn
toAC (lhs, args) = do
  let rArgs = args
  let len@(S k) = length rArgs
  | _ => MkAC lhs 0 [] [] [] empty
  let argVect = Vect.fromList rArgs
  let withRange = zip Vect.Fin.range argVect
  let ac' = foldl acfold (MkAC' [<] [<] empty) withRange
  MkAC lhs (length rArgs) argVect (toList ac'.explicits) (toList ac'.autos) ac'.nameds


public export
mkAC : {fvs : Nat} -> {bjn : Nat} -> IRTerm fvs bjn -> AppChain fvs bjn
mkAC x = toAC $ peelAppTelescope x

public export
unAC : AppChain fvs bjn -> IRTerm fvs bjn
unAC ac = applyAppTelescope ac.lhs (toList ac.args)
