-- Do not import Data.Vect

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

{- 1 -}

my_reverse : Vect n a -> Vect n a
my_reverse xs = reverse' [] xs
  where reverse' : Vect n a -> Vect m a -> Vect (n+m) a
        reverse' acc [] = ?reverseProof_nil acc
        reverse' acc (x :: xs)
                        = ?reverseProof_xs (reverse' (x::acc) xs)

{- 2 -}

head_unequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
           (contra : (x = y) -> Void) -> (x :: xs) = (y :: ys) -> Void

tail_unequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
          (contra : (xs = ys) -> Void) -> (x :: xs) = (y :: ys) -> Void


{- 3 -}

DecEq a => DecEq (Vect n a) where
