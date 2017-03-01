import Data.Vect

-- find an index of an element in the vector
vpos : (v : Vect n a) -> Elem x v -> Fin n
vpos (y :: xs) Here = FZ
vpos (y :: xs) (There later) = FS (vpos xs later)

vreplace : (v : Vect n a) -> Elem x v -> (y : a) -> (v : Vect n a ** Elem y v)
vreplace (x :: xs) Here y = (y :: xs ** Here)
vreplace (x :: xs) (There later) y with (vreplace xs later y)
  vreplace (x :: xs) (There later) y | (ys ** pf) = (x :: ys ** There pf)

vswap : (v1 : Vect n1 t ** Elem x v1) -> (v2 : Vect n2 t ** Elem y v2) ->
             ((v1':Vect n1 t ** Elem y v1'), (v2' : Vect n2 t ** Elem x v2'))
vswap (x::xs ** Here) (y::ys ** Here) = ((y :: xs ** Here), (x :: ys ** Here))
vswap (x::xs ** Here) (y::ys ** There later) with (vswap (x::xs ** Here) (ys ** later))
  | ((v1' ** e1), (v2' ** e2)) = ((v1' ** e1), (y::v2' ** There e2))
vswap (x::xs ** There later) (y::ys ** Here) with (vswap (xs ** later) (y::ys ** Here))
  | ((v1' ** e1), (v2' ** e2)) = ((x::v1' ** There e1), (v2' ** e2))
vswap (x::xs ** There later_x) (y::ys ** There later_y) with (vswap (xs ** later_x) (ys ** later_y))
  | ((v1' ** e1), (v2' ** e2)) = ((x :: v1' ** There e1), (y :: v2' ** There e2))


test_vswap_1 : Bool
test_vswap_1 =
  let ((xs ** _), (ys ** _)) = vswap ([1,2,3] ** Here) ([10,20,30] ** Here)
  in (xs, ys) == ([10,2,3], [1,20,30])

test_vswap_2 : Bool
test_vswap_2 =
  let ((xs ** t), (ys ** u)) = vswap ([1,2,3] ** Here) ([10,20,30] ** There Here)
  in (xs, ys) == ([20,2,3], [10,1,30])

test_vswap_3 : Bool
test_vswap_3 =
  let ((xs ** t), (ys ** u)) = vswap ([1,2,3] ** There Here) ([10,20,30] ** Here)
  in (xs, ys) == ([1,10,3], [2,20,30])

test_vswap_4 : Bool
test_vswap_4 =
  let ((xs ** t), (ys ** u)) = vswap ([1,2,3] ** There Here) ([10,20,30] ** There $ There Here)
  in (xs, ys) == ([1,30,3], [10,20,2])

test_vswap : Bool
test_vswap =
  test_vswap_1 &&
  test_vswap_2 &&
  test_vswap_3 &&
  test_vswap_4

-- relation over vector, natural number and number of occurences
data Occ : (x : Nat) -> (n : Nat) -> (xs : Vect m Nat) -> Type where
  OccNil : Occ x 0 Nil
  OccNext : Not (x=y) -> Occ x n xs -> Occ x n (y :: xs)
  OccMore : (x = y) -> Occ x n xs -> Occ x (S n) (y :: xs)

mkOcc : (x : Nat) -> (xs : Vect m Nat) -> (n : Nat ** Occ x n xs)
mkOcc x [] = (0 ** OccNil)
mkOcc x (y :: xs) with (decEq x y)
  mkOcc x (y :: xs) | (Yes prf) with (mkOcc x xs)
    mkOcc x (y :: xs) | (Yes prf) | (n ** occ) = (S n ** OccMore prf occ)
  mkOcc x (y :: xs) | (No contra) with (mkOcc x xs)
    mkOcc x (y :: xs) | (No contra) | (n ** occ) = (n ** OccNext contra occ)

-- relation over list and its last element
data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

implementation Uninhabited (Last [] x) where
    uninhabited LastOne impossible
    uninhabited (LastCons _) impossible

last123 : Last [1,2,3] 3
last123 = LastCons (LastCons LastOne)

mkNo1 : (contra : Last (x :: xs) value -> Void) -> Last (value :: (x :: xs)) value -> Void
mkNo1 contra (LastCons prf) = contra prf

mkNo2 : (f : (x = value) -> Void) -> (contra : Last xs value -> Void) -> Last (x :: xs) value -> Void
mkNo2 f contra LastOne = f Refl
mkNo2 f contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No absurd
isLast (x :: xs) value with (isLast xs value)
  isLast (x :: [value])   value  | (Yes LastOne)        = Yes (LastCons LastOne)
  isLast (x :: (y :: ys)) value  | (Yes (LastCons prf)) = Yes (LastCons (LastCons prf))
  isLast (x :: xs)        value  | (No contra) with (decEq x value)
    isLast (value :: [])        value | (No contra) | (Yes Refl) = Yes LastOne
    isLast (value :: (x :: xs)) value | (No contra) | (Yes Refl) = No (mkNo1 contra)
    isLast (x :: xs)            value | (No contra) | (No f)     = No (mkNo2 f contra)

isNo : Dec a -> Bool
isNo (Yes _) = False
isNo (No _)  = True

isYes : Dec a -> Bool
isYes = not . isNo

test_isLast : Bool
test_isLast =
  isNo  (isLast [1,2,3] 1) &&
  isNo  (isLast [1,2,3] 2) &&
  isYes (isLast [1,2,3] 3) &&
  isNo  (isLast [1,2,3] 4)

-- define relation over lists which is analogous to Elem
-- and implement its decision procedure
data LElem : List a -> a -> Type where
  HereIs : LElem (value :: xs) value
  ThereIs : (prf : (LElem xs value)) -> LElem (x :: xs) value

implementation Uninhabited (LElem [] a) where
    uninhabited HereIs impossible
    uninhabited (ThereIs _) impossible

isLElem_contra : (f : LElem xs value -> Void) -> (contra : (x = value) -> Void) -> LElem (x :: xs) value -> Void
isLElem_contra f contra HereIs = contra Refl
isLElem_contra f contra (ThereIs prf) = f prf

isLElem : DecEq a => (xs : List a) -> (value : a) -> Dec (LElem xs value)
isLElem [] value = No absurd
isLElem (x :: xs) value with (decEq x value)
  isLElem (value :: xs) value | (Yes Refl) = Yes HereIs
  isLElem (x :: xs) value | (No contra) with (isLElem xs value)
    isLElem (x :: (value :: ys)) value | (No contra) | (Yes HereIs) = Yes (ThereIs HereIs)
    isLElem (x :: (y :: ys)) value | (No contra) | (Yes (ThereIs prf)) = Yes (ThereIs (ThereIs prf))
    isLElem (x :: xs) value | (No contra) | (No f) = No (isLElem_contra f contra)

test_isLElem : Bool
test_isLElem =
  isNo  (isLElem [1,2,3] 0) &&
  isYes (isLElem [1,2,3] 1) &&
  isYes (isLElem [1,2,3] 2) &&
  isYes (isLElem [1,2,3] 3)
