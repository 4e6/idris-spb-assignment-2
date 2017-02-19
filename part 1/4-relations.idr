import Data.Vect

-- find an index of an element in the vector
vpos : (v : Vect n a) -> Elem x v -> Fin n

vreplace : (v : Vect n a) -> Elem x v -> (y : a) -> (v : Vect n a ** Elem y v)

vswap : (v1 : Vect n1 t ** Elem x v1) -> (v2 : Vect n2 t ** Elem y v2) ->
             ((v1':Vect n1 t ** Elem y v1'), (v2' : Vect n2 t ** Elem x v2'))

-- relation over vector, natural number and number of occurences
data Occ : (x : Nat) -> (n : Nat) -> (xs : Vect m Nat) -> Type where
  OccNil : Occ x 0 Nil
  OccNext : Not (x=y) -> Occ x n xs -> Occ x n (y :: xs)
  OccMore : (x = y) -> Occ x n xs -> Occ x (S n) (y :: xs)


mkOcc : (x : Nat) -> (xs : Vect m Nat) -> (n : Nat ** Occ x n xs)

-- relation list and its last element
data Last : List a -> a -> Type where
  LastOne : Last [item] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

last123 : Last [1,2,3] 3
last123 = LastCons (LastCons LastOne)

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)

-- define relation over lists which is analogous to Elem
-- and implement its decision procedure
data LElem : {- ??? -} Type where

isLElem : ?isLElem
