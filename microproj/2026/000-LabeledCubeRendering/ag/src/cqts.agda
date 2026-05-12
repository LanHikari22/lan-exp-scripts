{- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv -}
{- vPrimitive -}

LevelUniv = Agda.Primitive.LevelUniv
Level = Agda.Primitive.Level
ℓ-zero = Agda.Primitive.lzero
ℓ-suc = Agda.Primitive.lsuc
ℓ-max = Agda.Primitive._⊔_

Type = Set

{- ^Primitive -}
{- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ -}

{- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv -}
{- vDefining ℕ -}

open import Agda.Builtin.Nat

ℕ = Agda.Builtin.Nat.Nat

_∙_ : ℕ → ℕ → ℕ
_∙_ = Agda.Builtin.Nat._*_

infixl 7 _∙_

{- The following code sets up Agda to let us write numerals like `1`,
`2`, etc. and have it automatically interpreted as a natural number or
integer as appropriate. -}

record Number {ℓ : Level} (A : Set ℓ) : Set ℓ where
  field fromNat : ℕ → A

open Number {{...}} public using (fromNat)

record Negative {ℓ : Level} (A : Set ℓ) : Set ℓ where
  field fromNeg : ℕ → A

open Negative {{...}} public using (fromNeg)

{-# BUILTIN FROMNAT fromNat #-}
{-# DISPLAY Number.fromNat _ n = fromNat n #-}
{-# BUILTIN FROMNEG fromNeg #-}
{-# DISPLAY Negative.fromNeg _ n = fromNeg n #-}

instance
  Number-ℕ : Number ℕ
  Number-ℕ .fromNat n = n

{- ^Defining ℕ -}
{- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ -}

{- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv -}
{- vDefining Σ -}

open import Agda.Builtin.Sigma

infix 2 Σ-syntax

Σ-syntax : {ℓ ℓ' : Level} (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ-max ℓ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : {ℓ ℓ' : Level} (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
A × B = Σ[ a ∈ A ] B

infixr 5 _×_

{- ^Defining Σ -}
{- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ -}

{- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv -}
{- vPrelude -}

case_of_ : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → A → (A → B) → B
case x of f = f x

infix 0 case_of_

data Test-Id-Family {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  instance test-id-refl : Test-Id-Family x x

data Test-Identical {ℓ : Level} {A : Set ℓ} : Set ℓ where
  test-identical : (a a' : A) → {{Test-Id-Family a a'}} → Test-Identical

data Test-Type {ℓ : Level} : Set (ℓ-suc ℓ) where
  test-type : {A : Set ℓ} → (a : A) → (A' : Set ℓ) → {{Test-Id-Family A A'}} → Test-Type

{- ^Prelude -}
{- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ -}

double : ℕ → ℕ
double x = 2 ∙ x

idfunℕ : ℕ → ℕ
idfunℕ x = x

idfunᵉ : (A : Type) → (A → A)
idfunᵉ A x = x

{- Universal mapping in property for pair types -}

×-ump-to : {A : Type} → {B : Type} → {C : Type}
  → (C → A) → (C → B) → (C → A × B)
×-ump-to f g c = (f c , g c)

×-ump-fro : {A : Type} → {B : Type} → {C : Type} → (C → A × B) → (C → A) × (C → B)
×-ump-fro f = (λ c → f c .fst) , (λ c → f c .snd)

{- Forming the product type is functorial -}

×-mapⁱ : {A B C D : Type}
  → (A → B)
  → (C → D)
  → (A × C → B × D)
×-mapⁱ = λ f g (a , c) → (f a , g c )


{- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv -}
{- Bool -}

data Bool : Type where
  true  : Bool
  false : Bool

not : Bool → Bool
not b = case b of λ
  { true  → false
  ; false → true
  }

_and_ : Bool → Bool → Bool
_and_ x y = case x of λ
  { true  → case y of λ
            { true  → true
            ; false → false }
  ; false → false
  }

_xor_ : Bool → Bool → Bool
_xor_ x y = case x of λ
  { true  → case y of λ
            { true  → false 
            ; false → true }
  ; false → case y of λ 
            { true  → true
            ; false → false} } 

_or_ : Bool → Bool → Bool
x or y = case x of λ
  { true  → true
  ; false → y}

_implies_ : Bool → Bool → Bool
true  implies true  = true
true  implies false = false
false implies _     = true

{- /Bool -}
{- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ -}

{- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv -}
{- ⊤ -}

open import Agda.Builtin.Unit

{- Universal mapping in property for ⊤ -}

⊤-ump-in-to : {A : Type}
  → ⊤
  → (A → ⊤)
⊤-ump-in-to t = λ x → tt

⊤-ump-in-fro : {A : Type}
  → (A → ⊤)
  → ⊤
⊤-ump-in-fro f = tt

{-Universal mapping out property for ⊤ -}

⊤-ump-out-to : {A : Type}
  → A
  → (⊤ → A)
⊤-ump-out-to t = λ x → t

⊤-ump-out-fro : {A : Type}
  → (⊤ → A)
  → A
⊤-ump-out-fro f = f tt



{- /⊤ -}
{- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ -}

{- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv -}
{- ℕ -}

isZero : ℕ → Bool
isZero zero = true
isZero (suc n) = false

_ = test-identical (isZero 0) true
_ = test-identical (isZero 19) false

predℕ : ℕ → ℕ
predℕ zero    = zero
predℕ (suc n) = n

_ = test-identical (predℕ 0) 0
_ = test-identical (predℕ 1) 0
_ = test-identical (predℕ 19) 18

doubleℕ : ℕ → ℕ
doubleℕ zero    = zero
doubleℕ (suc n) = suc (suc (doubleℕ n))

isEven : ℕ → Bool
isOdd  : ℕ → Bool

isEven zero = true
isEven (suc n) = isOdd n

isOdd zero = false
isOdd (suc n) = isEven n

{- /ℕ -}
{- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ -}

{- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv -}
{- vLists -}


data List (A : Type) : Type where
  []    : List A                -- The empty list
  _::_  : A → List A → List A   -- The list with a head element and a tail remainder

[_] : {A : Type} → A → List A
[ a ] = a :: []

_++_ : {A : Type} → List A → List A → List A
[] ++ l2 = l2
(x :: l1) ++ l2 = x :: (l1 ++ l2)

length : {A : Type} → List A → ℕ
length [] = zero
length (x :: L) = 1 + (length L)

_ = test-identical (length [ tt ]) 1
_ = test-identical (length (1 :: 2 :: 3 :: [])) 3

ℕ→List⊤ : ℕ → List ⊤
ℕ→List⊤ zero = []
ℕ→List⊤ (suc n) = tt :: (ℕ→List⊤ n)

_ = test-identical (ℕ→List⊤ 0) []
_ = test-identical (ℕ→List⊤ 3) (tt :: tt :: tt :: [])

reverse : {A : Type} → List A → List A
reverse [] = []
reverse (x :: x₁) = (reverse x₁) ++ [ x ]

_ = test-identical (reverse [ 1 ]) [ 1 ]
_ = test-identical (reverse (1 :: 2 :: 3 :: [])) (3 :: 2 :: 1 :: [])

{- ^Lists -}
{- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ -}

{- vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv -}
{- vℤ -}

data ℤ : Type where
  pos    : ℕ → ℤ
  negsuc : ℕ → ℤ

negℕ : ℕ → ℤ
negℕ zero = pos zero
negℕ (suc n) = negsuc n

instance
  Number-ℤ : Number ℤ
  Number-ℤ .fromNat = pos

  Negative-ℤ : Negative ℤ
  Negative-ℤ .fromNeg = negℕ

_ = test-identical 2 (pos (suc (suc (zero))))
_ = test-identical -3 (negsuc (suc (suc (zero))))

sucℤ : ℤ → ℤ
sucℤ (pos n) = pos (suc n)
sucℤ (negsuc zero) = pos (zero)
sucℤ (negsuc (suc n)) = (negsuc n)

_ = test-identical (sucℤ 19) 20
_ = test-identical (sucℤ -1) 0
_ = test-identical (sucℤ 0) 1
_ = test-identical (sucℤ 1) 2
_ = test-identical (sucℤ -34) -33

predℤ : ℤ → ℤ
predℤ (pos zero) = (negsuc zero)
predℤ (pos (suc n)) = (pos n)
predℤ (negsuc n) = (negsuc (suc n))

_ = test-identical (predℤ 19) 18
_ = test-identical (predℤ 0) -1
_ = test-identical (predℤ 1) 0
_ = test-identical (predℤ 2) 1
_ = test-identical (predℤ -34) -35

-- This should correspond to $z + n$, where $n$ is a natural number
_+pos_ : ℤ → ℕ → ℤ
pos a +pos b = (pos (a +ℕ b))
-- -(a+1) + b = -a -1 +b = --a + b -1 = (pred --a + b)
-- -(0+1) + b = pred b
-- -((S a)+1) + b = -(S a) -1 + b = --(S a) + (pred b) = (negsuc a) + (pred b)
negsuc zero +pos b = (predℤ (pos b))
negsuc (suc a) +pos zero = negsuc (suc a)
negsuc (suc a) +pos suc b = (negsuc a) +pos b

-- This should correspond to $z + -(n+1)$, where $n$ is a natural number
_+negsuc_ : ℤ → ℕ → ℤ
a +negsuc zero = (predℤ a)
-- a + --((S b) + 1) = a + --(S b) + --1 = (pred a) + (negsuc b)
a +negsuc suc b = (predℤ a) +negsuc b

_+ℤ_ : ℤ → ℤ → ℤ
m +ℤ (pos n) = m +pos n
m +ℤ (negsuc n) = m +negsuc n

_ = test-identical (-1 +ℤ -1) -2
_ = test-identical (-1 +ℤ 0) -1
_ = test-identical (-1 +ℤ 1) 0
_ = test-identical (0 +ℤ -1) -1
_ = test-identical (0 +ℤ 0) 0
_ = test-identical (0 +ℤ 1) 1
_ = test-identical (1 +ℤ -1) 0
_ = test-identical (1 +ℤ 0) 1
_ = test-identical (1 +ℤ 1) 2
_ = test-identical (19 +ℤ 34) 53
_ = test-identical (-19 +ℤ 34) 15


-_ : ℤ → ℤ
- pos zero = pos zero
- pos (suc a) = negsuc a
- negsuc a = pos (suc a)

_ = test-identical (- 0) 0
_ = test-identical (- 19) (-19)
_ = test-identical (- (-34)) 34

_-ℤ_ : ℤ → ℤ → ℤ
m -ℤ n = m +ℤ (- n)


_·ℤ_ : ℤ → ℤ → ℤ
pos zero ·ℤ z = pos zero
pos (suc n) ·ℤ z = z +ℤ ((pos n) ·ℤ z)
negsuc zero ·ℤ z = - z
negsuc (suc n) ·ℤ z = (- z) +ℤ ((negsuc n) ·ℤ z)

_ = test-identical (0 ·ℤ 0) 0
_ = test-identical (2 ·ℤ 3) 6
_ = test-identical (2 ·ℤ -3) -6
_ = test-identical (-2 ·ℤ 3) -6
_ = test-identical (-2 ·ℤ -3) 6
_ = test-identical (-1 ·ℤ 5) -5
_ = test-identical (9 ·ℤ -1) -9

{- ^Z -}
{- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ -}
