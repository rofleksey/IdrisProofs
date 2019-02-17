%default total

DivBy : Nat -> Nat -> Type
DivBy a b = (n : Nat ** a = b * n)

task: DivBy a b -> DivBy b c -> DivBy a c
task {a=a} {b=b} {c=c} (n ** x) (m ** y) = (m*n ** right)
	where right = rewrite x in
	rewrite (multAssociative c m n) in
	rewrite y in
	Refl