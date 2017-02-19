same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys

same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
