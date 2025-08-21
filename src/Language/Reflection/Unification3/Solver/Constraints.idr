module Language.Reflection.Unification3.Solver.Constraints

import public Language.Reflection.Unification3.Context
import public Language.Reflection.Unification3.Error
import public Language.Reflection.Unification3.IR

import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.State

import Language.Reflection
import Language.Reflection.TT
import Language.Reflection.TTImp
import Language.Reflection.Syntax

import Data.Either
import Data.FinBitSet
import Data.Fin
import Data.Nat
import Data.Vect
import Data.SortedMap

%default total

public export
record ConstraintBucket (fvsL : Nat) (fvsR : Nat) where
  constructor MkCB
  members : FinBitSet
  equalsTo : Maybe $ Either (IRTerm fvsL 0) (IRTerm fvsR 0)

emptyCB : ConstraintBucket fvsL fvsR
emptyCB = MkCB empty Nothing

Show (ConstraintBucket fvsL fvsR) where
  show cb = "MkCB \{show cb.members} \{show cb.equalsTo}"

public export
record Constraints (fvsL : Nat) (fvsR : Nat) where
  buckets : Nat
  bucketData : Vect buckets $ ConstraintBucket fvsL fvsR
  fvLToBucket : Vect fvsL $ Fin buckets
  fvRToBucket : Vect fvsR $ Fin buckets

Show (Constraints fvsL fvsR) where
  show cs = "MkConstraints \{show cs.bucketData}"

bucketOf : Either (Fin fvsL) (Fin fvsR) -> 
           Constraints fvsL fvsR -> 
           ConstraintBucket fvsL fvsR
bucketOf (Left fv) cs = flip index cs.bucketData $ index fv cs.fvLToBucket
bucketOf (Right fv) cs = flip index cs.bucketData $ index fv cs.fvRToBucket

setBucketOf : Either (Fin fvsL) (Fin fvsR) ->
              ConstraintBucket fvsL fvsR ->
              Constraints fvsL fvsR ->
              Constraints fvsL fvsR
setBucketOf (Left i) cb cs =
  { bucketData $= replaceAt (index i cs.fvLToBucket) cb } cs
setBucketOf (Right i) cb cs = 
  { bucketData $= replaceAt (index i cs.fvRToBucket) cb } cs

transferVariables : List (Fin a) -> Fin b  -> Vect a (Fin b) -> Vect a (Fin b)
transferVariables vars bucket m = foldr (flip replaceAt bucket) m vars

addBucket : {fvsL, fvsR : Nat} -> 
            ConstraintBucket fvsL fvsR -> 
            Constraints fvsL fvsR -> 
            Constraints fvsL fvsR
addBucket b = 
  { buckets $= S
  , bucketData $= flip snoc b . map {members $= removeAll b.members}
  , fvLToBucket $= transferVariables (toList b.members) last . map weaken
  , fvRToBucket $= transferVariables (toList b.members) last . map weaken
  }

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

