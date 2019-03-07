%default total

minmax: (a:Nat) -> (b: Nat) -> maximum a (minimum a b) = a
minmax Z Z = Refl
minmax (S x) Z = Refl
minmax Z (S y) = Refl
minmax (S x) (S y) = rewrite (minmax x y) in Refl