<!--
```
{-# OPTIONS --allow-unsolved-metas #-}
module 2--Paths-and-Identifications.2-1--Paths where

open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 1--Type-Theory.1-5--Propositions-as-Types
```
-->


# Lecture 2-1: Paths

In Lecture 1-5, we saw that we could define types that represent
equality in another inductive type, like ``Bool`` or ``ℕ``. It would
be tedious to have to define equality separately for every type (and
worse, to check that every function preserves equality), and it would
make proving general facts about equality difficult.

To resolve this issue, Cubical Type Theory takes a page from homotopy
theory --- the mathematical theory of continuous deformations of
shapes. Classically, a *homotopy* is a continuous deformation of one
object into another. In homotopy theory, we only care about the
properties of objects which are unchanged by continuous deformation;
so for the purposes of homotopy theory, to give a homotopy between
objects is to say that they are the same, at least for all
homotopy-theoretical purposes. In other words, to a homotopy theorist,
a homotopy is a way to say two things are the same.

We will use this as inspiration for the concept of sameness that will
apply to all types. Let's see a bit more of the classical theory
first, so we have something to ground our intuitions.

If $f, g : X → Y$ are two continuous functions between spaces $X$ and
$Y$ (say, subsets of Euclidean space), then a homotopy $h$ between $f$
and $g$ is a function $h : [0, 1] × X → Y$ of two variables $h(t, x)$
where $h(0, x) = f(x)$ and $h(1, x) = g(x)$ for all $x$. So, for a
fixed $x$, the function $t ↦ h(t, x)$ traces out a path in $Y$ from
$f(x)$ to $g(x)$. By packing these paths together into a single
function $[0, 1] × X → Y$, the idea is that $h(t, x)$ continuously
transforms the function $f$ into the function $g$ as $t$ travels from
$0$ to $1$.

<!--
::: Aside:
If you are reading this in your editor, we are using the `$` symbol to
delimit mathematical expressions as opposed to type theoretic ones;
admittedly the difference is not too important.
:::
-->

As we saw in Lecture 1-1, we can think of a function with two
arguments as a function with one argument that gives back another
function with one argument (via ``×-curry`` and ``×-uncurry``). In
this case, we can see a homotopy $h$ between $f$ and $g$ as a function
$h : [0, 1] → (X → Y)$ into the space of continuous functions $X → Y$,
so that $h(0) = f$ and $h(1) = g$. In other words, a homotopy is a
*path* in a function space, where by path we mean a continuous
function out of the unit interval $[0, 1]$.

In general, if objects $F$ and $G$ are points that live in some space
$S$, then a homotopy between $F$ and $G$ is a path $h : [0, 1] → S$
with $h(0) = F$ and $h(1) = G$.

::: Aside:
Before we begin: The following block lets us refer to some
arbitrary types `A`, `B`, ... and terms `x : A`, `y : A`, ... without
cluttering every definition with `{A : Type} {B : Type}`, and so on.

```
private
  variable
    ℓ ℓ' ℓ₂ ℓ₃ : Level
    A B C D : Type ℓ
    x y : A
```
:::


## Paths

Let's translate this into type theory. Agda provides a special "type"
``I`` to act as a version of the unit interval $[0, 1]$, equipped with
two elements `i0 : I` and `i1 : I`, which act as the endpoints $0$ and
$1$. A *path* `x ≡ y` from `x` to `y` of type `A` will be a function
`h : I → A` where `h i0` is identical to `x` and `h i1` is identical
to `y`. Agda remembers the endpoints of a path, so that when we later
evaluate the path at `i0`, we do get `x` exactly, and similarly for
`i1` and `y`.

Similarly to ``Level``, the interval ``I`` is not actually a type,
rather, we are just using it as a tool to describe our notion of
sameness. For this reason, it gets siloed in its own special universe,
``IUniv``.

This prevents us from using all our usual type operations on
``I``, which is good, since an element of ``I`` isn't meant
to be treated as a piece of data.

```
-- Uncomment these and try them out, if you want!
-- _ : Type
-- _ = I × I  -- error!

-- _ : Type
-- _ = Bool → I -- error!
```

::: Aside:
Above we make a "definition" with name `_`; this signals to Agda to
check the type of what we provide, but then throw away the result. We
will use this to demonstrate the type of some expression without
having to invent a new name for it.
:::

However, since we want to discuss paths in any type, there is a
special rule that for any actual type `A : Type ℓ`, functions `I → A`
is also an actual type in `Type ℓ`.

```
_ : Type ℓ-zero
_ = I → Bool
```

Now we for paths with specified endpoints. For `x` and `y`, Agda
provides a built-in type `x ≡ y` which is like a function `I → A`, but
where the endpoints are known to be exactly `x` and `y`. That is,
starting with `p : x ≡ y`, evaluating `p i0` gives *exactly* `x`, and
evaluating `p i1` gives *exactly* `y`, regardless of what the
definition of the path `p` actually is.

New paths `x ≡ y` in a type `A` are defined the same way that
functions are: we assume we have an `i : I`, and then give an element
of the type `A`. Agda will make sure that we indeed get `x` when `i`
is ``i0`` and `y` when `i` is ``i1``.

The simplest path we can write down is the reflexivity path: for any
element `x`, there is a constant path at `x`.

```
refl : {x : A} → x ≡ x
refl {x = x} i = x
```

Interpreted as a statement about sameness, this means that `x` is the
same as `x` --- certainly a good start!

Even with only ``refl`` we are already able to prove some useful
equalities. For example, The type ``Bool`` has the structure of a
*Boolean algebra*, with respect to ``and`` and ``or``. Here are some
of the axioms:

```
or-idl : (x : Bool) → false or x ≡ x
or-idl x = refl

or-idr : (x : Bool) → x or false ≡ x
or-idr false = refl
or-idr true  = refl

or-comm : (x y : Bool) → x or y ≡ y or x
or-comm false false = refl
or-comm false true  = refl
or-comm true  false = refl
or-comm true  true  = refl

or-LEM : (x : Bool) → x or (not x) ≡ true
-- Exercise:
or-LEM true = refl
or-LEM false = refl

or-assoc : (x y z : Bool) → x or (y or z) ≡ (x or y) or z
-- Exercise:
or-assoc true true true = refl
or-assoc true true false = refl
or-assoc true false true = refl
or-assoc true false false = refl
or-assoc false true true = refl
or-assoc false true false = refl
or-assoc false false true = refl
or-assoc false false false = refl
```

OK, that's enough of that --- it's straightforward to keep going.

::: Aside:
You can find all the laws for a Boolean algebra listed on Wikipedia,
or you can peek ahead to Lecture 2-2 and take all the laws for a De Morgan
algebra (but where `∧ = and` and `∨ = or` and `~ = not`) together with
the "Law of Excluded Middle": `b or (not b)`.
:::

::: Aside:
The `≡` constructor has low precedence, so `x or y ≡ y or x` means
`(x or y) ≡ (y or x)`, and not something weird like `x or (y ≡ y) or x`.
:::

A type of paths is a type like any other, so we can define functions
that accept paths as arguments and produce paths as results. It is
easy to show that any function sends equal inputs to equal outputs.

```
apⁿ : (f : A → B)
  → x ≡ y
  → f x ≡ f y
apⁿ f p i = f (p i)
```

Here, we are composing the function `f` with the "function" `x ≡ y`.
When we plug in `i = i0`, we get that the left endpoint is `f (p i0)`,
which is `f x`, and when we plug in `i = i1`, we similarly get the
right endpoint as `f (p i1)`, i.e. `f y`. So indeed, this defines a
path `f x ≡ f y`.

```
apⁿ-bin : (f : A → B → C) {a a' : A} {b b' : B}
  → a ≡ a'
  → b ≡ b'
  → f a b ≡ f a' b'
-- Exercise:
apⁿ-bin f p q i = f (p i) (q i)

apⁿ-∘ : (f : A → B) (g : B → C)
  → (p : x ≡ y)
  → apⁿ (g ∘ f) p ≡ apⁿ g (apⁿ f p)
-- Exercise:
-- apⁿ-∘ f g p i = {!!}
-- apⁿ-∘ f g p = {!!}
-- apⁿ-∘ f g p i i₁ = {!!}
apⁿ-∘ f g p i i₁ = g (f (p i₁))
```

``apⁿ`` is simple but useful. For example, we can re-prove some of the
properties of addition (``+ℕ-≡ℕ-idl``, ``+ℕ-≡ℕ-idr``, ``+ℕ-≡ℕ-assoc``)
using our new notion of equality. These proofs will have the same
structure as the previous ones, doing case-splitting on the first
argument to simplify the goal. In each recursive step, you will have
to use ``apⁿ`` to convert a path `n ≡ m` to a path `suc n ≡ suc m`.
(We didn't have to do that previously, because `suc n ≡ℕ suc m` was
*defined* to be `n ≡ℕ m`. Win some lose some!)

```
+ℕ-idl : (n : ℕ) → (zero +ℕ n) ≡ n
-- Exercise:
+ℕ-idl n = refl

+ℕ-idr : (n : ℕ) → (n +ℕ zero) ≡ n
-- Exercise:
+ℕ-idr zero = refl
+ℕ-idr (suc n) = apⁿ suc (+ℕ-idr n)

+ℕ-assoc : (n m k : ℕ) → (n +ℕ (m +ℕ k)) ≡ ((n +ℕ m) +ℕ k)
-- Exercise:
+ℕ-assoc zero m k = refl
+ℕ-assoc (suc n) m k = apⁿ suc (+ℕ-assoc n m k)
```

Another use is to show that the constructors for inductive types are
injective. If the same constructor is used on both endpoints of a
path, we can peel that constructor off.

```
suc-inj : {x y : ℕ} → suc x ≡ suc y → x ≡ y
-- Exercise: (Hint: use ``predℕ``!)
suc-inj p = apⁿ predℕ p

inl-inj : {x y : A} → Path (A ⊎ B) (inl x) (inl y) → x ≡ y
inl-inj {A = A} {x = x} p = apⁿ uninl p
  where
    uninl : A ⊎ B → A
    uninl (inl a) = a
    uninl (inr _) = x

inr-inj : {x y : B} → Path (A ⊎ B) (inr x) (inr y) → x ≡ y
-- Exercise:
inr-inj {B = B} {x = x} p = apⁿ uninr p
  where
    uninr : A ⊎ B → B
    uninr (inl _) = x
    uninr (inr a) = a
```

Here we use the alternative name ``Path`` to construct the type of
paths rather than ``≡`` so that we can specify the type that the path
exists in. If we just write `inl x ≡ inl y` then Agda can see that the
left side of ``⊎`` has to be `A` because `x : A` and `y : A`, but it
has no way of knowing that the right side should be `B`!


## Inductive Types with Path Constructors

How can we get our hands on some more interesting paths? One way is to
define inductive types that have path constructors. (These are often
called "Higher Inductive Types" or HITs.)

Our first use of a path constructor is a more symmetrical version of
the integers. Remember that the definition of ``ℤ`` we gave back in
Lecture 1-2 is a little janky --- we have to treat the negative
integers and the positive integers asymmetrically, assigning ``zero``
to the ``pos`` side and shifting the ``negsuc`` side down by one. Now
that we have paths, we can define a symmetric version of the integers
as two copies of the the natural numbers, one for the positive
integers and one for the negative --- as long as we add in a
path between "positive 0" and "negative 0" to make them the same!

```
data ℤˢ : Type where
  posˢ : ℕ → ℤˢ
  negˢ : ℕ → ℤˢ
  zeroˢ≡ : posˢ zero ≡ negˢ zero
```

Arithmetic using these integers is easier to reason about than the
version involving ``negsuc``. First, here's the successor function,
which you should compare to the previous definition ``sucℤ``.

```
-- sucℤ : ℤ → ℤ
-- sucℤ (pos n) = pos (suc n)
-- sucℤ (negsuc zero) = pos (zero)
-- sucℤ (negsuc (suc n)) = (negsuc n)

sucℤˢ : ℤˢ → ℤˢ
sucℤˢ (posˢ x) = posˢ (suc x)
sucℤˢ (negˢ zero) = posˢ (suc zero)
sucℤˢ (negˢ (suc x)) = negˢ x
sucℤˢ (zeroˢ≡ i) = posˢ (suc zero)
```

On positive integers, we use the ordinary successor of the enclosed
natural number. On negative integers, we check if the natural number
is zero, and if so, give back positive one, and use the enclosed
predecessor otherwise.

Notice that we have defined what the function does on zero twice! Once
as `posˢ zero`, and again as `negˢ zero`. The final case for the path
constructor ``zeroˢ≡`` forces us to demonstrate that we give the same
answer both times. And indeed we do, so final case can be defined by
the constant path at `posˢ (suc zero)`.

It is easy to convert between these integers and the original ones.
For the forward direction, most of the cases are straightforward; only
``zeroˢ≡`` we have to think about. Here, remember that typing `C-c
C-,` will have Agda show you the type of what it wants to see,
including the boundary restrictions if you are in the process of
defining a path. In this case, assuming have defined the other cases
of the function correctly, we need a term of ``ℤ`` that is equal to
`pos zero` when `i = i0`, and also equal to `pos zero` when `i = i1`.
For this, we can obviously just use `pos zero` itself.

```
ℤˢ→ℤ : ℤˢ → ℤ
-- Exercise:
ℤˢ→ℤ (posˢ x) = pos x
ℤˢ→ℤ (negˢ zero) = pos (zero)
ℤˢ→ℤ (negˢ (suc x)) = negsuc x
ℤˢ→ℤ (zeroˢ≡ i) = pos zero
-- 

ℤ→ℤˢ : ℤ → ℤˢ
-- Exercise:
ℤ→ℤˢ (pos x) = posˢ x
ℤ→ℤˢ (negsuc x) = negˢ (suc x)

-- No cheating!
_ = test-identical (ℤˢ→ℤ (ℤ→ℤˢ -2)) -2
_ = test-identical (ℤˢ→ℤ (ℤ→ℤˢ -1)) -1
_ = test-identical (ℤˢ→ℤ (ℤ→ℤˢ 0)) 0
_ = test-identical (ℤˢ→ℤ (ℤ→ℤˢ 1)) 1
_ = test-identical (ℤˢ→ℤ (ℤ→ℤˢ 2)) 2
```

Complete the definition of addition. The cases for ``zeroˢ≡`` will all
involve constant paths. If you are writing ``zeroˢ≡`` on the
right-hand side somewhere, you have gone astray!

```
predℤˢ : ℤˢ → ℤˢ
-- Exercise:
predℤˢ (posˢ zero) = negˢ (suc zero)
predℤˢ (posˢ (suc x)) = posˢ x
predℤˢ (negˢ x) = negˢ (suc x)
predℤˢ (zeroˢ≡ i) = negˢ (suc zero)

_ = test-identical (predℤˢ (ℤ→ℤˢ 0)) (ℤ→ℤˢ -1)
_ = test-identical (predℤˢ (ℤ→ℤˢ 1)) (ℤ→ℤˢ 0)
_ = test-identical (predℤˢ (ℤ→ℤˢ 2)) (ℤ→ℤˢ 1)
_ = test-identical (predℤˢ (ℤ→ℤˢ -1))  (ℤ→ℤˢ -2)
_ = test-identical (predℤˢ (ℤ→ℤˢ -2))  (ℤ→ℤˢ -3)

_+ℤˢ_ : ℤˢ → ℤˢ → ℤˢ
-- Exercise:
-- m +ℤˢ n = {!!}
posˢ zero +ℤˢ n = n
posˢ (suc x) +ℤˢ n = sucℤˢ ((posˢ x) +ℤˢ n)
negˢ zero +ℤˢ n = n
negˢ (suc x) +ℤˢ n = predℤˢ ((negˢ x) +ℤˢ n)
zeroˢ≡ i +ℤˢ n = n

_ = test-identical ((ℤ→ℤˢ 1)  +ℤˢ (ℤ→ℤˢ 0))  (ℤ→ℤˢ 1)
_ = test-identical ((ℤ→ℤˢ 1)  +ℤˢ (ℤ→ℤˢ 1))  (ℤ→ℤˢ 2)
_ = test-identical ((ℤ→ℤˢ -1) +ℤˢ (ℤ→ℤˢ 0))  (ℤ→ℤˢ -1)
_ = test-identical ((ℤ→ℤˢ -1) +ℤˢ (ℤ→ℤˢ 1))  (ℤ→ℤˢ 0)
_ = test-identical ((ℤ→ℤˢ -1) +ℤˢ (ℤ→ℤˢ -1)) (ℤ→ℤˢ -2)
```

The simplest non-trivial type involving a path constructor is the
*circle* ``S¹``, so named because it contains a point ``base`` and a
path ``loop`` which goes from ``base`` to ``base``, forming a circle.

```
data S¹ : Type where
  base : S¹
  loop : base ≡ base
```

There's not a huge amount we can do with ``S¹`` without technology
from later lectures, but we can at least describe its recursion
principle. The recursion principle for the circle states that to
produce a function `S¹ → A` for any type `A`, we need to specify a
point `a : A`, and a loop `l : a ≡ a` starting and ending at that
point. In other words, to produce a function `S¹ → A`, we just need to
draw a circle in the type `A`.

```
S¹-rec : {A : Type ℓ}
  → (a : A)
  → a ≡ a
  → S¹ → A
S¹-rec a l base = a
S¹-rec a l (loop i) = l i
```

You may be able to guess that this forms part of a universal mapping
property. Not only can we build a function `S¹ → A` out of a point and
a loop in `A`, but we can go back.

```
S¹-ump-fro : {A : Type ℓ}
  → (S¹ → A)
  → Σ[ a ∈ A ] a ≡ a
-- Exercise:
S¹-ump-fro f = (f base) , refl
```


## Paths in Pair and Function Types

Now we can ask what paths look like in various types. Inductive data
types (like ``Bool``) will be covered in detail in Lecture 2-3. Let's
begin with something easier: what is a path in a pair type? It's a
pair of paths.

To prove these, remember that any path in `A` is secretly a function
`I → A` so, ignoring the endpoints, the first exercise is asking for a
function `(I → A) × (I → B) → (I → A × B)`. It should be easy to come
up with such a function, and it turns out that this obvious definition
has the correct endpoints.

```
×≡→≡× : {x y : A × B} → (x .fst ≡ y .fst) × (x .snd ≡ y .snd) → x ≡ y
-- Exercise:
×≡→≡× (p₁ , p₂) i = (p₁ i) , (p₂ i)

≡×→×≡ : {x y : A × B} → x ≡ y → (x .fst ≡ y .fst) × (x .snd ≡ y .snd)
-- Exercise:
≡×→×≡ p = (apⁿ fst p) , apⁿ snd p
```

Similarly, what is a path in a function type? This brings us full
circle to the classical definition of homotopy: it is a function
landing in paths! In type theory this is known as the principle of
"function extensionality": to claim that `f` is the same as `g` means
claiming that, for all `x`, `f x` is the same as `g x`.

```
funextˢ : {f g : A → B}
  → ((x : A) → f x ≡ g x)
  → f ≡ g
-- Exercise:
funextˢ px i x = px x i

funextˢ⁻ : {f g : A → B}
  → f ≡ g
  → ((x : A) → f x ≡ g x)
-- Exercise:
funextˢ⁻ p x i = p i x

-- funext : ((x : A) → (f x ≡ g x)) → f ≡ g
-- funext h i x = h x i

-- funext⁻ : f ≡ g → ((x : A) → (f x ≡ g x))
-- funext⁻ p x i = p i x
```

(We write ``funextˢ`` in anticipation of proving a more general fact
for dependent functions ``funext``, later in this Lecture.)

This works for functions with any number of arguments:

```
funext₂ : {f g : A → B → C}
  → (p : (x : A) (y : B) → f x y ≡ g x y)
  → f ≡ g
-- Exercise:
funext₂ p i x y = p x y i
```

Try using ``funextˢ`` to prove some unsurprising facts about function
composition:

```
∘-assoc : (h : C → D)
        → (g : B → C)
        → (f : A → B)
        → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
-- Exercise:
∘-assoc c→d b→c a→b = funextˢ (λ x i → c→d (b→c (a→b x)))

∘-idl : (f : A → B) → idfun ∘ f ≡ f
-- Exercise:
∘-idl f = funextˢ (λ x i → f x)

∘-idr : (f : A → B) → f ∘ idfun ≡ f
-- Exercise:
∘-idr f i x = f x
```


## Paths over Paths

A path in a type `A` is a function `p : I → A` with fixed endpoints 
`x : A` and `y : A`. But what if `A` is itself a path of types
`A : I → Type`? Then we consider dependent functions `p : (i : I) → A i`
with fixed endpoints `x : A i0` and `y : A i``; these are called
"paths over the path `A`", or sometimes simply "path-overs". The name
for this in Agda is ``PathP``, for "Path (over) P(ath)". This is
another built-in notion, like ``≡``.

```
_ : (A : I → Type) (x : A i0) (y : A i1) → Type
_ = PathP
```

Similarly to paths, if we have `p : PathP A x y`, then `p i0` is `x` and
`p i1` is `y` always, regardless of the actual definition of `p`.

In fact, the type `x ≡ y` is defined in terms of ``PathP``, where the
path of types happens to be the constant path at the type `A`. This is
just like how non-dependent functions `A → B` are exactly dependent
functions `(x : A) → B`, where `B` happens to be a constant type and
not depend on `x`.

Try re-defining ``≡`` out of ``PathP``:

```
≡-again : (A : Type) (x : A) (y : A) → Type
-- Exercise: (easy)
≡-again A x y = A
```

We can upgrade ``apⁿ`` to apply to dependent functions:

```
-- Exercise:

-- apⁿ : (f : A → B)
--   → x ≡ y
--   → f x ≡ f y
-- apⁿ f p i = f (p i)

ap : {B : A → Type ℓ₂} 
     → {x y : A}
     → (f : (a : A) → B a)
     → (p : x ≡ y)
     → PathP (λ i → B (p i)) (f x) (f y)
--     → PathP {!!} {!!} {!!}

ap f p i = f (p i)

-- Exercise:
ap-bin :
     {B : A → Type ℓ₂}
     {C : (x : A) → B x → Type ℓ₃}
     (f : (x : A) → (y : B x) → C x y)
     {a a' : A} {b : B a} {b' : B a'}
     → (p : a ≡ a')
     → (q : PathP (λ i → B (p i)) b b')
     → PathP (λ i → C (p i) (q i)) (f a b) (f a' b')
    --  → PathP {!!} {!!} {!!}
    --  → (q : PathP {!!} {!!} {!!})
    --  → PathP {!!} {!!} {!!}

ap-bin f p q i ={!!}
```

Let's return to paths in pair types, but look at *dependent* pairs.
There are actually two places dependency could show up here. The first
is the obvious one, when `B` depends on `A`. The definitions are the
same as in the non-dependent case, that is, the functions ``×≡→≡×``
and ``≡×→×≡``, so try to fill in the parameters to the ``PathP`` type.

::: Aside:
Here we are going to use an "anonymous module", to collect the
parameters `A`, `B`, `x` and `y` that are identical between the two
exercises ``ΣPathP→PathPΣ'`` and ``PathPΣ→ΣPathP'``.
:::

```
-- ×≡→≡× : {x y : A × B} → (x .fst ≡ y .fst) × (x .snd ≡ y .snd) → x ≡ y
-- ×≡→≡× (p₁ , p₂) i = (p₁ i) , (p₂ i)

-- ≡×→×≡ : {x y : A × B} → x ≡ y → (x .fst ≡ y .fst) × (x .snd ≡ y .snd)
-- ≡×→×≡ p = (apⁿ fst p) , apⁿ snd p

module _ {A : Type ℓ} {B : A → Type ℓ₂}
  {x y : Σ[ a ∈ A ] B a}
  where

  -- Exercise:
  ΣPathP→PathPΣ' : Σ[ p ∈ (fst x ≡ fst y) ] (PathP (λ i → B (p i)) (snd x) (snd y))
         → x ≡ y
  ΣPathP→PathPΣ' (p₁ , p₂) i = (p₁ i) , p₂ i

  -- Exercise:
  PathPΣ→ΣPathP' : x ≡ y
         → Σ[ p ∈ (fst x ≡ fst y) ] (PathP (λ i → B (p i)) (snd x) (snd y))
  PathPΣ→ΣPathP' s = (ap fst s) , (ap snd s)
```

There is a second possible notion of dependency: it could be that the
types `A` and `B` themselves are paths of types, that is, they depend
on an element of ``I``. Again, the actual definitions are
identical; but their types become more powerful.

```
module _ {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₂}
  {x : Σ[ a ∈ A i0 ] B i0 a} {y : Σ[ a ∈ A i1 ] B i1 a}
  where

  -- Exercise:
  ΣPathP→PathPΣ : Σ[ p ∈ PathP (λ i → A i) (fst x) (fst y) ] PathP (λ i → B i (p i)) (snd x) (snd y)
         → PathP (λ i → Σ[ a ∈ A i ] B i a) x y
  ΣPathP→PathPΣ (p₁ , p₂) i = (p₁ i) , (p₂ i)

  -- Exercise:
  PathPΣ→ΣPathP : PathP (λ i → Σ[ a ∈ A i ] B i a) x y
         → Σ[ p ∈ PathP (λ i → A i) (fst x) (fst y) ] PathP (λ i → B i (p i)) (snd x) (snd y)
  PathPΣ→ΣPathP s .fst i = fst (s i)
  PathPΣ→ΣPathP s .snd i = (snd (s i))
```

And now dependent functions. Similarly to what we have just seen for
Σ-types, there are lots of ways to add dependency to the arguments of
function extensionality. The most obvious is to allow `B` to depend on
`A`, not involving the cubical interval:

```
module _ {A : Type ℓ} {B : A → Type ℓ₂}
  {f g : (a : A) → B a}
  where
  funext : ((x : A) → (f x ≡ g x)) → f ≡ g
  funext h i x = h x i
  
  funext⁻ : f ≡ g → ((x : A) → (f x ≡ g x))
  funext⁻ p x i = p i x
```

Path-overs are also what is required to describe the *induction*
principle of the circle; the upgraded version of ``S¹-rec`` for
dependent functions. If we have a type family `A : S¹ → Type` over the
circle rather than just a single type, the provided point must be an
element of the type family at ``base``, and the loop is a path from
that point to itself, lying over the path of types `A ∘ loop`.

```
S¹-ind : {A : S¹ → Type ℓ}
  → (a : A base)
  → PathP (λ i → A (loop i)) a a
  → (s : S¹) → A s
S¹-ind a l base = a
S¹-ind a l (loop i) = l i
```

The input `l : PathP (λ i → A (loop i)) a a` involves a path `λ i → A
(loop i)` from `A base` to itself, that is, a path between two
*types*. Right now we have no way of producing interesting paths
between types, but univalence will come to the rescue in Lecture 2-6.


## Squares

A path in a type of paths is a function with shape `a : I → (I → A)`.
This is equivalent (again via something like ``×-curry``) to a function
`I × I → A`, and we can therefore think of paths-between-paths as
functions of two interval variables `i` and `j`. Though we can't use
the elements of `I` as data and so don't let ourselves actually form
the type `I × I`, we can nevertheless think of a function of two
interval variables corresponding to a square.

             a-₁
       a₀₁ — — — > a₁₁
        ^           ^             ^
    a₀- |           | a₁-       j |
        |           |             ∙ — >
       a₀₀ — — — > a₁₀              i
             a-₀

How do we properly write down the type of such a thing? Well, let's
imagine we have a square like that and we feed it a value of `i`. What
should the type of the result be? Well, once we've chosen an `i`,
what's left is a function `I → A` which is awaiting a value of `j`,
that is, the result is a vertical slice of the above square. We can
even identify what the endpoints of that slice should be: once we've
chosen a value of `i`, we know that vertical slice starts at `a-₀ i`
on the bottom, and ends up at `a-₁ i` on the top.

```
Square-sweep : {A : Type ℓ} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  → (a-₀ : a₀₀ ≡ a₁₀) (a-₁ : a₀₁ ≡ a₁₁)
  → (I → Type ℓ)
Square-sweep a-₀ a-₁ i = a-₀ i ≡ a-₁ i
```

Now this is true for any value of `i`, including `i = i0` and
`i = i1`. In those cases, we know exactly which vertical paths we
should get: the left and right boundaries of the square.

So putting this all together, as `i` travels from ``i0`` to ``i1``, we
want a value of `Square-sweep a-₀ a-₁ i` that travels from `a₀-` to
`a₁-`. This is our definition of what it means to be a ``Square`` with
specified boundary.

```
Square : {A : Type ℓ} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  → (a₀- : a₀₀ ≡ a₀₁)
  → (a₁- : a₁₀ ≡ a₁₁)
  → (a-₀ : a₀₀ ≡ a₁₀)
  → (a-₁ : a₀₁ ≡ a₁₁)
  → Type ℓ
Square a₀- a₁- a-₀ a-₁ = PathP (Square-sweep a-₀ a-₁) a₀- a₁-
```

Let's define some simple squares. If we start with a path `x ≡ y` and
think of it lying horizontally, we can stretch it vertically into a
square.

             p
         x — — — > y
         ^         ^                  ^
    refl |         | refl           j |
         |         |                  ∙ — >
         x — — — > y                    i
             p

```
stretch-vertical : (p : x ≡ y) → Square refl refl p p
stretch-vertical p i j = p i
```

So the value of the square at any point is given by forgetting the
second dimension (`j`) and doing whatever the path `p` does on `i`.

```
stretch-horizontal : (p : x ≡ y) → Square p p refl refl
-- Exercise:
stretch-horizontal p i j = p j
```

For some practice thinking with squares, write a version of ``ap``
that applies to squares.

             a-₁                              ap f a₁-
       a₀₁ — — — > a₁₁                  f a₁₀ — — — > f a₁₁
        ^           ^                      ^           ^
    a₀- |           | a₁-   ~~>   ap f a-₀ |           | ap f a-₁
        |           |                      |           |
       a₀₀ — — — > a₁₀                  f a₀₀ — — — > f a₀₁
             a-₀                              ap f a₀-

```
ap-Square : (f : A → B)
  → {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  → {a₀- : Path A a₀₀ a₀₁}
  → {a₁- : Path A a₁₀ a₁₁}
  → {a-₀ : Path A a₀₀ a₁₀}
  → {a-₁ : Path A a₀₁ a₁₁}
  → Square a₀- a₁- a-₀ a-₁
  → Square (ap f a₀-) (ap f a₁-) (ap f a-₀) (ap f a-₁)
-- Exercise:
ap-Square f s i i₁ = f (s i i₁)
```

Next, write down the function that flips a square along the diagonal:


             a-₁                           a₁-
       a₀₁ — — — > a₁₁               a₁₀ — — — > a₁₁
        ^           ^                 ^           ^
    a₀- |           | a₁-   ~~>   a-₀ |           | a-₁
        |           |                 |           |
       a₀₀ — — — > a₁₀               a₀₀ — — — > a₀₁
             a-₀                           a₀-

```
flip-square : {a₀₀ a₀₁ a₁₀ a₁₁ : A }
  → {a₀- : Path A a₀₀ a₀₁}
  → {a₁- : Path A a₁₀ a₁₁}
  → {a-₀ : Path A a₀₀ a₁₀}
  → {a-₁ : Path A a₀₁ a₁₁}
  → Square a₀- a₁- a-₀ a-₁
  → Square a-₀ a-₁ a₀- a₁-
-- Exercise:
flip-square s i j = s j i
```

Given two functions `f` and `g` from `A` to `B` and a path `a ≡ a'` in
`A`, we can use `ap` on each of those functions to get two paths that
live in `B`. Given a homotopy `H` between `f` and `g`, we can fill in
a square between those two paths:

           ap g p
       g a — — — > g a'
        ^           ^
    H a |           | H a'
        |           |
       f a — — — > f a'
           ap f p

```
homotopy-Path : {f g : A → B}
  → (H : (x : A) → (f x ≡ g x))
  → {a a' : A}
  → (p : a ≡ a')
  → Square (H a) (H a') (ap f p) (ap g p)
-- Exercise:
homotopy-Path H p i j = H (p i) j
```

Elements of the `Square A` type are squares that exist in a constant
type `A`. But just as we can upgrade ``Path`` to ``PathP`` where the
type `A` can vary over the path, we can upgrade ``Square`` to
``SquareP`` where the type can vary over the square.

```
SquareP :
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
  (a₀- : PathP (λ j → A i0 j) a₀₀ a₀₁)
  (a₁- : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a-₀ : PathP (λ i → A i i0) a₀₀ a₁₀)
  (a-₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → Type ℓ
SquareP A a₀- a₁- a-₀ a-₁
  = PathP (λ i → PathP (λ j → A i j) (a-₀ i) (a-₁ i))
          a₀-
          a₁-
```

Try to define a similar function ``flip-squareP``, where the type now
varies over the square. Here, the trick is not so much the definition
itself --- it will be the same as ``flip-square`` --- but rather the
type.

```
flip-squareP :
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
  {a₀- : PathP (λ j → A i0 j) a₀₀ a₀₁}
  {a₁- : PathP (λ j → A i1 j) a₁₀ a₁₁}
  {a-₀ : PathP (λ i → A i i0) a₀₀ a₁₀}
  {a-₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
     → SquareP A a₀- a₁- a-₀ a-₁
     → SquareP (λ i j → A j i) a-₀ a-₁ a₀- a₁-
flip-squareP A s i j = s j i
-- Exercise:
--      → SquareP {!!} {!!} {!!} {!!} {!!}
--      → SquareP {!!} {!!} {!!} {!!} {!!}
-- flip-squareP A s = {!!}
```


## Higher Path Constructors

Inductive types can also contain path-of-path constructors. Here's a
nice example: the torus, which consists a basepoint, two circles
connected to that basepoint, and a square region with sides as
follows:

              loop1
        base — — — > base
          ^           ^
          |           |                 ^
    loop2 |           | loop2         j |
          |           |                 ∙ — >
        base — — — > base                 i
              loop1

This really does correspond to the doughnut shape you might be
thinking of. By specifying the horizontal sides and vertical sides of
the square to be identical, we are gluing them together, much as in
the following animation:

<https://commons.wikimedia.org/wiki/File:Torus_from_rectangle.gif>

```
data Torus : Type where
  torus-base  : Torus
  torus-loop1  : torus-base ≡ torus-base
  torus-loop2  : torus-base ≡ torus-base
  torus-square : Square torus-loop2 torus-loop2 torus-loop1 torus-loop1
```

Topologically, the torus is equal to the product of two circles.
Imagine taking a single vertical circle on the torus that runs through
the middle. Then dragging this along a path made of a horizontal
circle, we trace out the full shape of the torus.

We can prove this equivalence directly, by pattern matching!

```
Torus→S¹×S¹ : Torus → S¹ × S¹
-- Exercise:
Torus→S¹×S¹ torus-base = base , base
Torus→S¹×S¹ (torus-loop1 i) = (loop i) , base
Torus→S¹×S¹ (torus-loop2 i) = base , (loop i)
Torus→S¹×S¹ (torus-square i i₁) = loop i , loop i₁

S¹×S¹→Torus : S¹ × S¹ → Torus
-- Exercise:
S¹×S¹→Torus (base , base) = torus-base
S¹×S¹→Torus (base , loop i) = torus-loop2 i
S¹×S¹→Torus (loop i , base) = torus-loop1 i
S¹×S¹→Torus (loop i , loop i₁) = torus-square i i₁
```

## References and Further Reading

* Agda Documentation
  * [The interval and path types](https://agda.readthedocs.io/en/latest/language/cubical.html#the-interval-and-path-types)
  * [Inductive types with path constructors](https://agda.readthedocs.io/en/latest/language/cubical.html#higher-inductive-types)
* Tutorial for `cubicaltt`, an early cubical proof assistant
  * [Paths](https://github.com/mortberg/cubicaltt/blob/master/lectures/lecture1.ctt)

These use a different notion of path, but many properties are similar.
* The original *[Homotopy Type Theory]* book:
  * Homotopies: Chapter 2.4
  * Paths in Σ types: Chapters 2.6 and 2.7
  * Function Extensionality: Chapter 2.9
  * The Circle: Chapter 6.4
* Egbert Rijke's *[Introduction to Homotopy Type Theory]*:
  * Function Extensionality: Chapter 13
  * The Circle: Chapter 21
* Martin Escardo's [Lecture Notes]:
  * [Paths in Σ types](https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmaequality)
* HoTTEST Summer School 2022
  * [The Circle](https://github.com/martinescardo/HoTTEST-Summer-School/blob/main/Agda/HITs/Lecture4-notes.lagda.md)

[Introduction to Homotopy Type Theory]: https://arxiv.org/abs/2212.11082
[Lecture Notes]: https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/index.htmlure-Notes/HoTT-UF-Agda.html
