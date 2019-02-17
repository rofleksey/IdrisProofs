%default total

DivBy : Nat -> Nat -> Type
DivBy a b = (n : Nat ** a = b * n)

divByZeroFail: DivBy (S Z) Z -> Void
divByZeroFail (n ** Refl) impossible

helper: (a:Nat) -> (b:Nat) -> S (plus a (plus a (mult b (S a)))) = Z -> Void
helper a b y = SIsNotZ {x=plus a (plus a (mult b (S a)))} y

divByBigFail: DivBy (S Z) (S (S b)) -> Void
divByBigFail {b=b} (Z ** x)     = void (SIsNotZ {x=Z} f)
    where f = rewrite x in rewrite (multZeroRightZero b) in Refl
divByBigFail {b=b} ((S a) ** x) = void (helper a b g)
	where g = sym (rewrite (plusSuccRightSucc a (plus a (mult b (S a)))) in succInjective Z (plus a (S (plus a (mult b (S a))))) x)

task: DivBy (S Z) a -> a = (S Z)
task {a=Z} t         = void (divByZeroFail t)
task {a=(S Z)} t     = Refl
task {a=(S (S n))} t = void (divByBigFail t)