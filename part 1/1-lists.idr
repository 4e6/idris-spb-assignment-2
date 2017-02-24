same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons {x} prf = cong {f = (::) x} prf

same_cons' : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons' Refl = Refl

cong2 : {f : a -> b -> c} -> (x = y) -> (t = u) -> f x t = f y u
cong2 Refl Refl = Refl

same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists {x} {y} prf_xy prf_xsys = cong2 {f = (::)} prf_xy prf_xsys

same_lists' : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists' Refl Refl = Refl
