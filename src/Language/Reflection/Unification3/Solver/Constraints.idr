module Language.Reflection.Unification3.Solver.Constraints

import public Language.Reflection.Unification3.Context
import public Language.Reflection.Unification3.Error
import public Language.Reflection.Unification3.IR

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
record ConstraintBucket (fvsL : Nat) (fvsR : Nat) where
  constructor MkCB
  membersL : FinBitSet
  membersR : FinBitSet
  equalsTo : Maybe $ Either (IRTerm fvsL 0) (IRTerm fvsR 0)

public export
emptyCB : ConstraintBucket fvsL fvsR
emptyCB = MkCB empty empty Nothing

public export
Show (ConstraintBucket fvsL fvsR) where
  show cb = "MkCB \{show cb.membersL} \{show cb.membersR} \{show cb.equalsTo}"

public export
record Constraints (fvsL : Nat) (fvsR : Nat) where
  constructor MkConstraints
  buckets : Nat
  bucketData : Vect buckets $ ConstraintBucket fvsL fvsR
  fvLToBucket : Vect fvsL $ Fin buckets
  fvRToBucket : Vect fvsR $ Fin buckets

public export
Show (Constraints fvsL fvsR) where
  show cs = "MkConstraints \{show cs.bucketData}"

public export
baseBuckets : 
  (fvsL : Nat) -> 
  (fvsR : Nat) -> 
  ( Vect fvsL (ConstraintBucket fvsL fvsR)
  , Vect fvsR (ConstraintBucket fvsL fvsR)
  )
baseBuckets fvsL fvsR = 
  ( (\f => MkCB (insert f empty) empty Nothing) <$> allFins fvsL
  , (\f => MkCB empty (insert f empty) Nothing) <$> allFins fvsR
  )

public export
baseConstraints : (fvsL : Nat) -> (fvsR : Nat) -> Constraints fvsL fvsR
baseConstraints fvsL fvsR = do
  let (indicesL, indicesR) = 
    splitAt fvsL $ Data.Vect.allFins $ fvsL + fvsR
  let (bucketsL, bucketsR) = baseBuckets fvsL fvsR
  MkConstraints (fvsL + fvsR) (bucketsL ++ bucketsR) indicesL indicesR

public export
bucketOf : Either (Fin fvsL) (Fin fvsR) -> 
           Constraints fvsL fvsR -> 
           ConstraintBucket fvsL fvsR
bucketOf (Left fv) cs = flip index cs.bucketData $ index fv cs.fvLToBucket
bucketOf (Right fv) cs = flip index cs.bucketData $ index fv cs.fvRToBucket

public export
setBucketOf : Either (Fin fvsL) (Fin fvsR) ->
              ConstraintBucket fvsL fvsR ->
              Constraints fvsL fvsR ->
              Constraints fvsL fvsR
setBucketOf (Left i) cb cs =
  { bucketData $= replaceAt (index i cs.fvLToBucket) cb } cs
setBucketOf (Right i) cb cs = 
  { bucketData $= replaceAt (index i cs.fvRToBucket) cb } cs

public export
transferVariables : List (Fin a) -> Fin b  -> Vect a (Fin b) -> Vect a (Fin b)
transferVariables vars bucket m = foldr (flip replaceAt bucket) m vars

public export
addBucket : {fvsL, fvsR : Nat} -> 
            ConstraintBucket fvsL fvsR -> 
            Constraints fvsL fvsR -> 
            Constraints fvsL fvsR
addBucket b = 
  { buckets $= S
  , bucketData $= flip snoc b . map {membersL $= removeAll b.membersL, membersR $= removeAll b.membersR}
  , fvLToBucket $= transferVariables (toList b.membersL) last . map weaken
  , fvRToBucket $= transferVariables (toList b.membersR) last . map weaken
  }

public export
mergeIntoAndUpdate : (cs : Constraints fvsL fvsR) -> 
                     Fin cs.buckets -> 
                     Fin cs.buckets ->
                     List (Either (Fin fvsL) (Fin fvsR)) ->
                     ConstraintBucket fvsL fvsR ->
                     Constraints fvsL fvsR
mergeIntoAndUpdate cs a b vars newData =
  { fvLToBucket $= transferVariables (lefts vars) a
  , fvRToBucket $= transferVariables (rights vars) a
  , bucketData $= replaceAt a newData . replaceAt b emptyCB
  } cs

