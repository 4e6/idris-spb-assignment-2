plus_n_zero : (n : Nat) -> n + 0 = n
plus_n_zero Z = Refl
plus_n_zero (S k) = rewrite plus_n_zero k in Refl

plus_right_one_succ : (n: Nat) -> n + 1 = S (n + 0)
plus_right_one_succ Z = Refl
plus_right_one_succ (S k) = rewrite plus_right_one_succ k in Refl

plus_n_succ : (n, k : Nat) -> n + (S k) = S (n + k)
plus_n_succ Z k = Refl
plus_n_succ (S j) k = rewrite plus_n_succ j k in Refl

plus_assoc : (a, b, c : Nat) -> a + (b + c) = (a + b) + c
plus_assoc Z b c = Refl
plus_assoc (S k) b c =
  let inductiveHypothesis = plus_assoc k b c in
  rewrite inductiveHypothesis in Refl

succ_inj : (n, m : Nat) -> S n = S m -> n = m
succ_inj m m Refl = Refl

plus_eq : (n, m, m' : Nat) -> n + m = n + m' -> m = m'
plus_eq Z m m' prf = prf
plus_eq (S k) m m' prf =
  let inductiveHypothesis = plus_eq k m m'
  in inductiveHypothesis (succ_inj (plus k m) (plus k m') prf)

plus_right_zero : (n, m : Nat) -> n + m = n -> m = 0
plus_right_zero Z m prf = prf
plus_right_zero (S k) m prf =
  let inductiveHypothesis = plus_right_zero k m
  in inductiveHypothesis (succ_inj _ _ prf)

-- if x > y then y <= x
gt__lte : x `GT` y -> y `LTE` x
gt__lte (LTESucc LTEZero) = LTEZero
gt__lte (LTESucc (LTESucc x)) = LTESucc (gt__lte (LTESucc x))

not_lte__succ : (j : Nat) -> (k : Nat) -> (p : Not (LTE (S j) (S k))) -> Not (LTE j k)
not_lte__succ _ _ p = \lte_jk => p (LTESucc lte_jk)

-- if not(x <= y) then (y <= x)
not_lte__lte : Not (x `LTE` y) -> y `LTE` x
not_lte__lte {x = x} {y = Z} p = LTEZero
not_lte__lte {x = Z} {y = (S k)} p = void (p LTEZero)
not_lte__lte {x = (S j)} {y = (S k)} p = LTESucc (not_lte__lte (not_lte__succ j k p))
