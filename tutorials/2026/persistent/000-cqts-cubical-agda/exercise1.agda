data N : Type where
    zero : ℕ
    suc  : N -> N

_+_ : N -> N -> N
zero    + m = m
(suc n) + m = suc (n + m)

_*_ : N -> N -> ℕ
zero    * m = zero
(suc n) * m = m + (n * m)

infixl 6 _+_
infixl 7 _*_



three : N
three = 3