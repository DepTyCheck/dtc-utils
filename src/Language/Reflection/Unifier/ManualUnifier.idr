||| Second-generation unifier
|||
|||
||| The unification process is as follows:
||| 1. Convert lhs and rhs TTImp into the unifier's IR
||| 2. Run the constraint-solver on the resultant equation,
|||    receiving the free variable inter-equality and intermediate value info.
||| 3. Generate a dependency graph of free variable equality clusters
||| 4. Check whether the graph has any cycles, error if so
||| 5. Solve the dependency graph
||| 6. Determine which free variables in the equality cluster to keep
module Language.Reflection.Unifier.ManualUnifier

import public Language.Reflection.Unifier.ManualUnifier.Solver

record DepGraph (cs : Constraints bds) where
  constructor MkDG
  bucketDeps : Vect cs.buckets $ FinBitSet cs.buckets


getDepsImpl : IRTerm vs bjn -> State (FinBitSet vs) $ IRTerm vs bjn
getDepsImpl (IRFreeVar fv) = modify (insert fv) *> pure (IRFreeVar fv)
getDepsImpl x = pure x

getDeps : IRTerm vs bjn -> FinBitSet vs
getDeps x = execState empty $ mapMIR getDepsImpl x

getDeps' : {bds : Bounds} -> (cs : Constraints bds) -> Fin cs.buckets -> FinBitSet cs.buckets
getDeps' cs bId = do
  case index bId cs.bucketData |> equalsTo of
    Just (True ** val) => 
      fromList $ map (flip index cs.fvLToBucket) $ toList $ getDeps val
    Just (False ** val) => 
      fromList $ map (flip index cs.fvRToBucket) $ toList $ getDeps val
    Nothing => empty

mkDG : {bds : Bounds} -> (cs : Constraints bds) -> DepGraph cs
mkDG cs = MkDG $ getDeps' cs <$> allFins cs.buckets

detectCyclesOne : 
  (cs : Constraints bds) -> 
  DepGraph cs -> 
  (FinBitSet cs.buckets, FinBitSet cs.buckets) -> 
  Fin cs.buckets -> 
  (Bool, FinBitSet cs.buckets)

detectCyclesStep : 
  (cs : Constraints bds) -> 
  DepGraph cs -> 
  (FinBitSet cs.buckets, FinBitSet cs.buckets) -> 
  List (Fin cs.buckets) -> 
  (Bool, FinBitSet cs.buckets)
detectCyclesStep cs dg (stack, allVisited) [] = (False, allVisited)
detectCyclesStep cs dg (stack, allVisited) (x :: xs) = do
  let (isCycle', allV) = detectCyclesOne cs dg (stack, allVisited) x
  if isCycle' then (True, allV) else do
    let (isCycle2, allV2) = detectCyclesStep cs dg (stack, allVisited) xs
    (isCycle' || isCycle2, merge allV allV2)

detectCyclesOne cs dg (stack, allVisited) bucket = do
  let deps = index bucket dg.bucketDeps
  if (lookup bucket deps) then (True, insert bucket allVisited) else do
    detectCyclesStep cs dg (insert bucket stack, insert bucket allVisited) (toList deps)

detectCyclesAll : 
  (cs : Constraints bds) -> 
  DepGraph cs -> 
  FinBitSet cs.buckets -> 
  Bool
detectCyclesAll cs dg visited = do
  let nonVisitedL = toList $ invert visited
  case nonVisitedL of
    [] => False
    (x :: xs) => do
      let (False, visited) = 
        detectCyclesOne cs dg (empty, visited) x
      | _ => True
      detectCyclesAll cs dg visited

record FinalExpressions (cs : Constraints bds) where
  constructor MkFE
  inner : Vect cs.buckets $ Maybe TTImp

genFE : (cs : Constraints bds) -> FinalExpressions cs
genFE cs = 
  MkFE $ 
    (\x => x.equalsTo >>= (\(a ** b) => finalTTImp b)) <$> cs.bucketData

emptyFE : (cs : Constraints bds) -> FinalExpressions cs
emptyFE cs = MkFE $ replicate cs.buckets Nothing

genTTImp : 
  (cs : Constraints bds) -> 
  DepGraph cs -> 
  FinalExpressions cs -> 
  (isLeft : Bool) -> 
  fvsT isLeft bds -> 
  bvsT isLeft bds bjn -> 
  term isLeft bds bjn -> 
  Maybe TTImp
genTTImp cs dg fe True fv bv (IRFreeVar x) = do
  let bucket = index x cs.fvLToBucket
  let Just bucketEqTo = equalsTo $ index bucket cs.bucketData
  | _ => Just $ IVar EmptyFC $ freeVarName x fv
  index bucket fe.inner
genTTImp cs dg fe False fv bv (IRFreeVar x) = do
  let bucket = index x cs.fvRToBucket
  let Just bucketEqTo = equalsTo $ index bucket cs.bucketData
  | _ => Just $ IVar EmptyFC $ freeVarName x fv
  index bucket fe.inner
genTTImp cs dg fe isLeft fv bv (IRLocalVar x) = Just $ IVar EmptyFC $ boundVarName x bv
genTTImp cs dg fe isLeft fv bv (IRGlobalVar nm) = Just $ IVar EmptyFC nm
genTTImp cs dg fe isLeft fv bv IRType = Just $ IType EmptyFC
genTTImp cs dg fe isLeft fv bv (IRApp x y) = 
  IApp EmptyFC 
    <$> genTTImp cs dg fe isLeft fv bv x 
    <*> genTTImp cs dg fe isLeft fv bv y
genTTImp cs dg fe isLeft fv bv (IRAutoApp x y) = 
  IAutoApp EmptyFC 
    <$> genTTImp cs dg fe isLeft fv bv x 
    <*> genTTImp cs dg fe isLeft fv bv y
genTTImp cs dg fe isLeft fv bv (IRNamedApp x nm y) = 
  INamedApp EmptyFC 
    <$> genTTImp cs dg fe isLeft fv bv x 
    <*> pure nm 
    <*> genTTImp cs dg fe isLeft fv bv y
genTTImp cs dg fe isLeft fv bv (IRLam rig pinfo nm x y) = 
  ILam EmptyFC rig 
    <$> (traverse (genTTImp cs dg fe isLeft fv bv) pinfo)
    <*> pure (Just nm)
    <*> genTTImp cs dg fe isLeft fv bv x
    <*> genTTImp cs dg fe isLeft fv (bv :< (nm, x)) y
genTTImp cs dg fe isLeft fv bv (IRPi rig pinfo nm x y) = 
  IPi EmptyFC rig 
    <$> (traverse (genTTImp cs dg fe isLeft fv bv) pinfo)
    <*> pure (Just nm)
    <*> genTTImp cs dg fe isLeft fv bv x
    <*> genTTImp cs dg fe isLeft fv (bv :< (nm, x)) y
genTTImp cs dg fe isLeft fv bv (IRLet rig nm type val body) = 
  ILet EmptyFC EmptyFC rig nm
    <$> genTTImp cs dg fe isLeft fv bv type
    <*> genTTImp cs dg fe isLeft fv bv val
    <*> genTTImp cs dg fe isLeft fv (bv :< (nm, type)) body
genTTImp cs dg fe isLeft fv bv (IRPrim c) = 
  Just $ IPrimVal EmptyFC c

genBTTImp : 
  {bds : Bounds} ->
  (cs : Constraints bds) -> 
  DepGraph cs -> 
  FinalExpressions cs ->
  (FreeVars bds.fvsL, FreeVars bds.fvsR) ->
  ConstraintBucket bds ->
  Maybe TTImp
genBTTImp cs dg fe (fv, _) (MkCB _ _ (Just (True ** snd))) = do
  genTTImp cs dg fe True fv [<] snd
genBTTImp cs dg fe (_, fv) (MkCB _ _ (Just (False ** snd))) = 
  genTTImp cs dg fe False fv [<] snd
genBTTImp cs dg fe _ _ = Nothing

advanceFE : 
  {bds : Bounds} -> 
  (cs : Constraints bds) -> 
  DepGraph cs -> 
  (FreeVars bds.fvsL, FreeVars bds.fvsR) ->
  FinalExpressions cs -> 
  FinalExpressions cs
advanceFE cs dg fvPair fe = do
  let newBuckets = map (genBTTImp cs dg fe fvPair) cs.bucketData
  if map isJust newBuckets == map isJust fe.inner 
    then fe 
    else advanceFE cs dg fvPair (MkFE newBuckets)

mkFE :   
  MonadError UnificationError m =>
  {bds : Bounds} -> 
  (cs : Constraints bds) -> 
  (FreeVars bds.fvsL, FreeVars bds.fvsR) ->
  m $ FinalExpressions cs
mkFE cs fvPair = do
  let dg = mkDG cs
  let False = detectCyclesAll cs dg empty
  | _ => throwError DepCycleError
  pure $ advanceFE cs dg fvPair $ emptyFE cs