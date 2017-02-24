-- Do not import Data.Vect

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a

     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

{- 1 -}

plus_nz : (n : Nat) -> n + 0 = n
plus_nz Z = Refl
plus_nz (S k) =
  let inductiveHypothesis = plus_nz k in
  rewrite inductiveHypothesis in Refl

reverseProof_nil' : Vect n a -> Vect (plus n 0) a
reverseProof_nil' {n} xs = rewrite plus_nz n in xs

reverseProof_nil : Vect n a -> Vect (plus n 0) a
reverseProof_nil {n = Z} xs = xs
reverseProof_nil {n = (S k)} (x :: xs) =
  let inductiveHypothesis = reverseProof_nil xs
  in x :: inductiveHypothesis

reverseProof_xs : Vect ((S n) + m) a -> Vect (plus n (S m)) a
reverseProof_xs {n = Z} xs = xs
reverseProof_xs {n = (S k)} (x :: xs) = x :: reverseProof_xs xs

my_reverse : Vect n a -> Vect n a
my_reverse xs = reverse' [] xs
  where reverse' : Vect n a -> Vect m a -> Vect (n+m) a
        reverse' acc {n} [] = reverseProof_nil acc
        reverse' acc (x :: xs)
                            = reverseProof_xs (reverse' (x::acc) xs)

{- 2 -}

head_unequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
           (contra : (x = y) -> Void) -> (x :: xs) = (y :: ys) -> Void
head_unequal contra Refl = contra Refl

tail_unequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
          (contra : (xs = ys) -> Void) -> (x :: xs) = (y :: ys) -> Void
tail_unequal contra Refl = contra Refl


{- 3 -}

DecEq a => DecEq (Vect n a) where
    decEq {n = Z}     [] [] = Yes Refl
    decEq {n = (S k)} (x :: xs) (y :: ys) with (decEq x y, decEq xs ys)
      decEq {n = (S k)} (x :: xs) (x :: xs) | (Yes Refl, Yes Refl) = Yes Refl
      decEq {n = (S k)} (x :: xs) (y :: ys) | (No contra_hd, _) = No (head_unequal contra_hd)
      decEq {n = (S k)} (x :: xs) (y :: ys) | (_, No contra_tl) = No (tail_unequal contra_tl)

[alternative] DecEq a => DecEq (Vect n a) where
    decEq [] [] = Yes Refl
    decEq (x :: xs) (y :: ys) with (decEq x y)
      decEq (y :: xs) (y :: ys)   | (Yes Refl) with (decEq xs ys)
        decEq (y :: ys) (y :: ys) | (Yes Refl) | (Yes Refl) = Yes Refl
        decEq (y :: xs) (y :: ys) | (Yes Refl) | (No contra_tl) = No (tail_unequal contra_tl)
      decEq (x :: xs) (y :: ys)   | (No contra_hd) = No (head_unequal contra_hd)
