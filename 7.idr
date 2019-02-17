%default total

pow2: Nat -> Nat
pow2 x = x * x

minusZ: (a: Nat) -> minus a Z = a
minusZ Z     = Refl
minusZ (S x) = Refl

lteHelper: (a: Nat) -> (b: Nat) -> LTE (a `minus` b) (a+b)
lteHelper x Z         = rewrite (minusZ x) in 
    rewrite (plusZeroRightNeutral x) in lteRefl
lteHelper Z y         = LTEZero
lteHelper (S x) (S y) = rewrite (sym (plusSuccRightSucc x y)) 
    in (lteSuccRight (lteSuccRight (lteHelper x y)))

lteRight: (n: Nat) -> LTE a b -> LTE a (n+b)
lteRight {b=b} Z t     = t
lteRight {b=b} (S x) t = rewrite (plusSuccRightSucc x b) in
    lteRight x (lteSuccRight t)

lteAdd: LTE a b -> LTE c d -> LTE (c+a) (d+b)
lteAdd {d=d} x LTEZero                  = lteRight d x
lteAdd x (LTESucc {left=c} {right=d} y) = LTESucc (lteAdd x y)

ltePow2: LTE a b -> LTE (pow2 a) (pow2 b)
ltePow2 {a=Z} {b=Z} t         = LTEZero
ltePow2 {a=(S x)} {b=Z} t       impossible
ltePow2 {a=Z} {b=(S y)} t     = LTEZero
ltePow2 {a=(S x)} {b=(S y)} t = rewrite (multRightSuccPlus x x) in 
	rewrite (multRightSuccPlus y y) in 
	(LTESucc (lteAdd (lteAdd (ltePow2 (fromLteSucc t)) (fromLteSucc t)) (fromLteSucc t)))
	
lteImplSub: LTE n m -> n `minus` m = 0
lteImplSub {n=Z} {m=Z} l         = Refl
lteImplSub {n=Z} {m=(S y)} l     = Refl
lteImplSub {n=(S x)} {m=(S y)} l = rewrite (lteImplSub (fromLteSucc l)) in Refl 

task: (a: Nat) -> (b: Nat) -> (pow2 (a `minus` b)) `minus` (pow2 (a + b)) = 0
task x y = lteImplSub (ltePow2 (lteHelper x y))