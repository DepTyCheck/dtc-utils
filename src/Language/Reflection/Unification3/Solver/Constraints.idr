module Language.Reflection.Unification3.Solver.Constraints

import public Language.Reflection.Unification3.Context
import public Language.Reflection.Unification3.Error
import public Language.Reflection.Unification3.IR
import public Language.Reflection.Unification3.IR.AppChain


import public Control.Monad.Error.Either
import public Control.Monad.Error.Interface
import public Control.Monad.State

import public Language.Reflection
import public Language.Reflection.TT
import public Language.Reflection.TTImp
import public Language.Reflection.Syntax

import public Data.Either
import public Data.FinBitSet
import public Data.Fin
import public Data.Nat
import public Data.Vect
import public Data.SortedMap

%default total

public export
record Bounds where
  constructor MkBounds
  fvsL : Nat
  fvsR : Nat

public export
Show Bounds where
  show (MkBounds l r) = "MkBounds \{show l} \{show r}"

public export
record AllFreeVars (bds : Bounds) where
  constructor MkAFV
  fvL : FreeVars bds.fvsL
  fvR : FreeVars bds.fvsR

parameters 
  (isLeft : Bool)
  (b : Bounds)

  %inline
  public export
  thisFvs : Nat
  thisFvs = if isLeft then b.fvsL else b.fvsR

  %inline
  public export
  otherFvs : Nat
  otherFvs = if isLeft then b.fvsR else b.fvsL

  %inline
  public export
  term : Nat -> Type
  term = IRTerm thisFvs

  %inline
  public export
  fvsT : Type
  fvsT = FreeVars thisFvs

  %inline
  public export
  bvsT : Nat -> Type
  bvsT = BoundVars thisFvs

  %inline
  public export
  appChain : Nat -> Type
  appChain = AppChain thisFvs

%inline
public export
thisFv : (isLeft : Bool) -> (b : Bounds) -> AllFreeVars b -> FreeVars $ thisFvs isLeft b
thisFv isLeft b = if isLeft then fvL else fvR

%inline
public export
otherFv : (isLeft : Bool) -> (b : Bounds) -> AllFreeVars b -> FreeVars $ otherFvs isLeft b
otherFv isLeft b = if isLeft then fvR else fvL

public export
record ConstraintBucket (bds : Bounds)  where
  constructor MkCB
  membersL : FinBitSet
  membersR : FinBitSet
  equalsTo : Maybe (isLeft : Bool ** term isLeft bds 0)

public export
emptyCB : ConstraintBucket bds
emptyCB = MkCB empty empty Nothing

public export
Show (ConstraintBucket bds) where
  show cb = "MkCB \{show cb.membersL} \{show cb.membersR} \{show cb.equalsTo}"

public export
record Constraints (bds : Bounds) where
  constructor MkConstraints
  buckets : Nat
  bucketData : Vect buckets $ ConstraintBucket bds
  fvLToBucket : Vect bds.fvsL $ Fin buckets
  fvRToBucket : Vect bds.fvsR $ Fin buckets
  fords : List ((iL : Bool ** term iL bds 0), (iL : Bool ** term iL bds 0))

public export
Show (Constraints bds) where
  show cs = "MkConstraints bdata=\{show cs.bucketData} fords=\{show cs.fords}"

public export
baseBuckets : 
  (bds : Bounds) ->
  ( Vect bds.fvsL (ConstraintBucket bds)
  , Vect bds.fvsR (ConstraintBucket bds)
  )
baseBuckets bds = 
  ( (\f => MkCB (insert f empty) empty Nothing) <$> allFins bds.fvsL
  , (\f => MkCB empty (insert f empty) Nothing) <$> allFins bds.fvsR
  )

public export
baseConstraints : (bds : Bounds) -> Constraints bds
baseConstraints bds = do
  let (indicesL, indicesR) = 
    splitAt bds.fvsL $ Data.Vect.allFins $ bds.fvsL + bds.fvsR
  let (bucketsL, bucketsR) = baseBuckets bds
  MkConstraints (bds.fvsL + bds.fvsR) (bucketsL ++ bucketsR) indicesL indicesR []

public export
bIndexOf : (isLeft : Bool) ->
           Fin (thisFvs isLeft bds) ->
           (cs : Constraints bds) -> 
           Fin cs.buckets
bIndexOf True fv cs = index fv cs.fvLToBucket
bIndexOf False fv cs = index fv cs.fvRToBucket

public export
bucketOf : (isLeft : Bool) ->
           Fin (thisFvs isLeft bds) ->
           Constraints bds -> 
           ConstraintBucket bds
bucketOf True fv cs = flip index cs.bucketData $ index fv cs.fvLToBucket
bucketOf False fv cs = flip index cs.bucketData $ index fv cs.fvRToBucket

public export
setBucketOf : (isLeft : Bool) ->
              Fin (thisFvs isLeft bds) ->
              ConstraintBucket bds ->
              Constraints bds ->
              Constraints bds
setBucketOf True i cb cs =
  { bucketData $= replaceAt (index i cs.fvLToBucket) cb } cs
setBucketOf False i cb cs = 
  { bucketData $= replaceAt (index i cs.fvRToBucket) cb } cs

public export
transferVariables : List (Fin a) -> Fin b  -> Vect a (Fin b) -> Vect a (Fin b)
transferVariables vars bucket m = foldr (flip replaceAt bucket) m vars

public export
addBucket : {bds : Bounds} -> 
            ConstraintBucket bds -> 
            Constraints bds -> 
            Constraints bds
addBucket b = 
  { buckets $= S
  , bucketData $= flip snoc b . map {membersL $= removeAll b.membersL, membersR $= removeAll b.membersR}
  , fvLToBucket $= transferVariables (toList b.membersL) last . map weaken
  , fvRToBucket $= transferVariables (toList b.membersR) last . map weaken
  }

lefts' : List (isLeft : Bool ** Fin (thisFvs isLeft bds)) -> List (Fin (thisFvs True bds))
lefts' [] = []
lefts' ((False ** snd) :: xs) = lefts' xs
lefts' ((True ** snd) :: xs) = snd :: lefts' xs

rights' : List (isLeft : Bool ** Fin (thisFvs isLeft bds)) -> List (Fin (thisFvs False bds))
rights' [] = []
rights' ((False ** snd) :: xs) = snd :: rights' xs
rights' ((True ** snd) :: xs) = rights' xs

public export
mergeIntoAndUpdate : (cs : Constraints bds) -> 
                     Fin cs.buckets -> 
                     Fin cs.buckets ->
                     List (Fin bds.fvsL) ->
                     List (Fin bds.fvsR) ->
                     ConstraintBucket bds ->
                     Constraints bds
mergeIntoAndUpdate cs a b varsL varsR newData =
  { fvLToBucket $= transferVariables varsL a
  , fvRToBucket $= transferVariables varsR a
  , bucketData $= replaceAt a newData . replaceAt b emptyCB
  } cs

