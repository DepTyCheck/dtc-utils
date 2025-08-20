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

import Data.FinBitSet
import Data.Fin
import Data.Nat
import Data.Vect
import Data.SortedMap

%default total

public export
record ConstraintBucket (fvs : Nat) where
  constructor MkCB
  members : FinBitSet
  equalsTo : Maybe $ IRTerm fvs 0

emptyCB : ConstraintBucket fvs
emptyCB = MkCB empty Nothing

Show (ConstraintBucket fvs) where
  show cb = "MkCB \{show cb.members} \{show cb.equalsTo}"

public export
record Constraints (fvs : Nat) where
  buckets : Nat
  bucketsData : Vect buckets $ ConstraintBucket fvs
  fvToBucket : Vect fvs $ Fin buckets

Show (Constraints fvs) where
  show cs = "MkConstraints \{show cs.bucketsData}"

bucketOfVar : Fin fvs -> Constraints fvs -> ConstraintBucket fvs
bucketOfVar fv cs = flip index cs.bucketsData $ index fv cs.fvToBucket

setBucketOfVar : Fin fvs -> 
                ConstraintBucket fvs -> 
                Constraints fvs -> 
                Constraints fvs
setBucketOfVar i cb cs = 
  { bucketsData $= replaceAt (index i cs.fvToBucket) cb } cs

transferVariables : List (Fin a) -> Fin b  -> Vect a (Fin b) -> Vect a (Fin b)
transferVariables vars bucket m = foldr (flip replaceAt bucket) m vars

addBucket : {fvs : Nat} -> ConstraintBucket fvs -> Constraints fvs -> Constraints fvs
addBucket b = 
  { buckets $= S
  , bucketsData $= flip snoc b . map {members $= removeAll b.members}
  , fvToBucket $= transferVariables (toList b.members) last . map weaken
  }

mergeIntoAndUpdate : (cs : Constraints fvs) -> 
                     Fin cs.buckets -> 
                     Fin cs.buckets ->
                     List (Fin fvs) ->
                     ConstraintBucket fvs ->
                     Constraints fvs
mergeIntoAndUpdate cs a b vars newData =
  { fvToBucket $= transferVariables vars a
  , bucketsData $= replaceAt a newData . replaceAt b emptyCB
  } cs

