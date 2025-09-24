module Experiment

import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Either
import Data.Vect
import Data.Nat
import Data.SnocList
import Data.SnocVect
import Data.SortedMap
import Decidable.Equality
import Language.Reflection
import Language.Reflection.Syntax

import Data.FinBitSet

namespace ExpVect
  data VectNat : Nat -> Type where
    Nil : VectNat 0
    (::) : Nat -> VectNat x -> VectNat (S x)

  public export
  castImpl : VectNat a -> Vect a Nat
  castImpl [] = []
  castImpl (x :: xs) = x :: castImpl xs

  mInj1 : {a : Nat} -> {a' : Nat} -> {b : VectNat l} -> {b' : VectNat l} -> (ExpVect.(::) a b) = (ExpVect.(::) a' b') -> (a = a', b = b')
  mInj1 {a} {a' = a} {b} {b' = b} Refl = (Refl, Refl)

  mCong1 : {a : Nat} -> {a' : Nat} -> {b : VectNat l} -> {b' : VectNat l} -> (a = a', b = b') -> (ExpVect.(::) a b) = (ExpVect.(::) a' b')
  mCong1 {a} {a' = a} {b} {b' = b} (Refl, Refl) = Refl

  pInj1 : {a : Nat} -> {a' : Nat} -> {b : Vect l Nat} -> {b' : Vect l Nat} -> (Vect.(::) a b) = (Vect.(::) a' b') -> (a = a', b = b')
  pInj1 {a} {a' = a} {b} {b' = b} Refl = (Refl, Refl)

  Cast (VectNat a) (Vect a Nat) where
    cast = castImpl

  injImpl : {x : VectNat a} -> {y : VectNat a} -> (castImpl x = castImpl y) -> (x = y)
  injImpl {x = []} {y = []} r = Refl
  injImpl {x = (_ :: _)} {y = (_ :: _)} r = do
    let (eq0, eq1) = pInj1 r
    let eq1 = injImpl eq1
    mCong1 (eq0, eq1)

  Injective ExpVect.castImpl where
    injective = injImpl

  DecEq (Vect a Nat) => DecEq (VectNat a) where
    decEq x1 x2 = decEqInj {f=castImpl} $ decEq (castImpl x1) (castImpl x2)

  data T0 : Type where
    TCon : (n : Nat) -> Vect n Nat -> T0

  t0Inj : {n : Nat} -> {n' : Nat} -> {xs : Vect n Nat} -> {xs' : Vect n' Nat} -> (TCon n xs) = (TCon n' xs') -> (n = n', xs = xs')
  t0Inj {n} {n' = n} {xs} {xs' = xs} Refl = (Refl, Refl)

namespace V1N
  data Vect1Nat : Type where
    (::) : Nat -> Vect 0 Nat -> Vect1Nat
