module Data.FinBitSet

import Data.Bits

%default total

public export
record FinBitSet where
  constructor MkFBS
  inner : Integer

public export
empty : FinBitSet
empty = MkFBS zeroBits

public export
lookup : Fin v -> FinBitSet -> Bool
lookup f (MkFBS s) = testBit s $ finToNat f

public export
insert : Fin v -> FinBitSet -> FinBitSet
insert f (MkFBS s) = MkFBS $ setBit s $ finToNat f

public export
delete : Fin v -> FinBitSet -> FinBitSet
delete f (MkFBS s) = MkFBS $ clearBit s $ finToNat f

public export
fromList : List (Fin v) -> FinBitSet
fromList = foldl (flip insert) empty

public export
toList : {v : Nat} -> FinBitSet -> List (Fin v)
toList fbs = filter (flip lookup fbs) $ List.allFins v

public export
removeAll : FinBitSet -> FinBitSet -> FinBitSet
removeAll (MkFBS a) (MkFBS b) = MkFBS $ b .&. (complement a)

public export
merge : FinBitSet -> FinBitSet -> FinBitSet
merge (MkFBS a) (MkFBS b) = MkFBS $ a .|. b

toLN' : Nat -> Integer -> List Nat
toLN' x s = 
  if s == 0 
     then [] 
     else if testBit s 0 
                            -- Since s != 0, shiftR s 1 < s
      then x :: toLN' (S x) (assert_smaller s $ shiftR s 1)
      else toLN' (S x) (assert_smaller s $ shiftR s 1)

toLN : FinBitSet -> List Nat
toLN (MkFBS s) = toLN' 0 s

public export
Show FinBitSet where
  show fbs = "fromList \{show $ toLN fbs}"
