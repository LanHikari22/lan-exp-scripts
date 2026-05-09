<!--
```
module 2--Paths-and-Identifications.2-7--Propositions where

open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 1--Type-Theory.1-5--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport

private
  variable
    ℓ ℓ' : Level
    A B P : Type ℓ
```
-->


# Lecture 2-7: Propositions

In Lecture 1-5, we saw how to use types to represent propositions. But
not all types have a sensible interpretation as propositions: an
element of ``ℕ`` in some sense contains more information than the mere
fact of a proposition being true. How can we characterise which types
should be thought of as propositions?

Let's recall from Lecture 1-5 that when considering a type `A` as a
proposition, we think of an element `a : A` as a witness to the fact
that the proposition `A` is true. Once we've constructed at least one
witness like this, we don't particularly care about the details of the
construction: we don't want there to more than one way that the
proposition `1 + 1 ≡ 2` can be true.

We turn this observation into a definition: propositions are types
that have *at most* one element. This Lecture will be spent discussing
this notion of proposition and some of its properties.


## Contractible Types

Before we get to propositions, we'll start with a class of types that
is even simpler: types that are not just propositions, but *true*
propositions.

A *singleton* is a type consisting of exactly one element. In ordinary
set theory, if $a$ is an element of a set $A$, then the singleton
subset of $A$ containing $a$ is $\{ a \}$ which, to make crystal clear
that we are dealing with a subset of $A$, we could write more
pedantically as the set $\{ x ∈ A ∣ a = x \}$. This is the notion of
singleton we are going to use as our definition in type theory. For an
element of a type `a : A`, the singleton type at `a` is:

```
singleton : {A : Type ℓ} → (a : A) → Type ℓ
singleton {A = A} a = Σ[ x ∈ A ] a ≡ x
```

There is a unique element of `singleton a`, namely the pair `(a, refl)`.

```
singleton-center : (a : A) → singleton a
singleton-center a = (a , refl)
```

We would like to say in type theory that `singleton a` has a unique
element, so we need a way of expressing "has a unique element"
type-theoretically. For this, we use: 

```
∃! : Type ℓ → Type ℓ
∃! A = Σ[ x ∈ A ] ((y : A) → y ≡ x)
```

An element of `∃! A` demonstrates existence and uniqueness of elements
of `A`: an element `x : A` exists, and the function assigning to every
`y : A` a path `x ≡ y` means that it is unique. Homotopically
speaking, this means that the type `A` *contracts onto the point `x`*.
If we have an element of `∃! A` we say that `A` is *contractible*.

This concept comes up often enough will define a record to capture it
so that we can name the two components.

```
record isContr (A : Type ℓ) : Type ℓ where
  constructor isContrData
  field
    center : A
    contraction : (a : A) → center ≡ a

open isContr public
```

The type ``⊤`` was defined to have only the element ``tt``, so it is
easy to show it is contractible.

```
isContr-⊤ : isContr ⊤
-- Exercise:
isContr-⊤ .center = tt
isContr-⊤ .contraction tt = refl
```

Singletons should also have a unique element. 

```
isContr-singleton : (a : A) → isContr (singleton a)
-- Exercise: (Hint: You will need to use `J` or a connection.)
isContr-singleton a .center = singleton-center a
isContr-singleton a .contraction (a₁ , a₁ₚ) = P₀
  where
    P₀ : singleton-center a ≡ (a₁ , a₁ₚ)
    P₀ i .fst = a₁ₚ i
    P₀ i .snd j = a₁ₚ (i ∧ j)
```

There are inductive types other than ``⊤`` that we can show are
contractible. As a somewhat contrived example, consider the "fake"
interval type defined by

```
data Interval : Type where
  zero : Interval
  one  : Interval
  seg  : zero ≡ one
```

This interval contains no interesting information at all:

```
isContr-Interval : isContr Interval
-- Exercise:
isContr-Interval .center = zero
isContr-Interval .contraction zero = refl
isContr-Interval .contraction one = seg
isContr-Interval .contraction (seg i) j = seg (i ∧ j)
```

::: Aside:
This ``Interval`` is an ordinary type, in contrast to the built-in
interval ``I``. We can therefore use it like any other type; form
functions into it, look at paths in it, and so on. It does not contain
any of the magic that ``I`` does, however, so we can't define a
corresponding ``Path`` or ``hcomp``.
:::

The empty type ``∅`` is not contractible: it doesn't have any elements
at all.

```
¬isContr-∅ : ¬ isContr ∅
-- Exercise:
¬isContr-∅ ()
```

And neither is ``Bool``. Although elements of ``Bool`` certainly
exist, they're not unique.

```
¬isContr-Bool : ¬ isContr Bool
-- Exercise: (Hint: `true≢false`.)
¬isContr-Bool (isContrData true p) = true≢false (p false)
¬isContr-Bool (isContrData false p) = true≢false (sym (p true))
```


## Propositions

Now for general propositions. A type is a proposition when it has at
most one element. That is, for any two elements, there is a path
between them.

```
isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y
```

This definition doesn't actually promise that there are any elements
of `A`, just that if we *did* have two elements, they would be equal.
This is just as well, because not every proposition has a proof.

The type ``⊤`` is a proposition that has a proof ``tt`` --- truth.
Because its induction principle lets us assume any element of ``⊤`` is
exactly ``tt``, it's easy to show ``⊤`` is a proposition in this new
sense, by pattern matching.

```
isProp-⊤ : isProp ⊤
-- Exercise:
isProp-⊤ tt tt = refl
```

As we saw in Lecture 1-5, ``∅`` represents a proposition with no
proof --- falsity. If a type has no elements at all then it certainly
has at most one element:

```
isProp-∅ : isProp ∅
-- Exercise:
isProp-∅ () y
```

We can piggyback on these to prove that many of the types we defined
in Lecture 1-5 as "propositions" in fact are propositions in our new,
refined sense.

```
isProp-isOddP : (n : ℕ) → isProp (isOddP n)
isProp-isEvenP : (n : ℕ) → isProp (isEvenP n)

isProp-isOddP zero = isProp-∅
isProp-isOddP (suc n) = isProp-isEvenP n

isProp-isEvenP zero = isProp-⊤
isProp-isEvenP (suc n) = isProp-isOddP n
```

And observational equality:

```
isProp-≡Bool : (a b : Bool) → isProp (a ≡Bool b)
isProp-≡Bool true true = isProp-⊤
isProp-≡Bool true false = isProp-∅
isProp-≡Bool false true = isProp-∅
isProp-≡Bool false false = isProp-⊤

isProp-≡ℕ : (n m : ℕ) → isProp (n ≡ℕ m)
-- Exercise:
isProp-≡ℕ zero zero = isProp-⊤
isProp-≡ℕ zero (suc m) = isProp-∅
isProp-≡ℕ (suc n) zero = isProp-∅
isProp-≡ℕ (suc n) (suc m) = isProp-≡ℕ n m
```

Contractible types may be thought of as types with a unique element.
Of course, a type with *exactly* one element also has *at most* one
element, so contractible types are also propositions.

```
isContr→isProp : isContr A → isProp A
-- Exercise:
isContr→isProp (isContrData ac ac-p) a b =
  a  ≡⟨ sym (ac-p a) ⟩ 
  ac ≡⟨ ac-p b ⟩
  b  ∎
```

The same is not true the other way, of course. We saw that ``∅`` is a
proposition but isn't contractible. Not being inhabited is the only
thing missing for a proposition to be contractible: as soon as a
proposition has an element, that element is unique.

```
isProp-with-point→isContr : isProp A → A → isContr A
-- Exercise:
isProp-with-point→isContr p a .center = a
isProp-with-point→isContr p a .contraction a₁ = p a a₁
```

Conversely, if assuming that a type is inhabited causes it to be
contractible, then that type must be a proposition to being with:

```
with-point-isContr→isProp : (A → isContr A) → isProp A
-- Exercise:
with-point-isContr→isProp c x y = 
  x               ≡⟨ sym ((c x) .contraction x) ⟩
  (c x) .center   ≡⟨ (c x) .contraction y ⟩
  y               ∎
```

Of course, the point of having a definition like ``isProp`` is that
not all types are propositions.

```
¬isProp-Bool : ¬ isProp Bool
-- Exercise:
¬isProp-Bool pBool = true≢false (pBool true false)

¬isProp-ℕ : ¬ isProp ℕ
-- Exercise:
¬isProp-ℕ pℕ = zero≢suc (pℕ zero (suc zero))
```


## Propositions, Equivalences and Retracts

Any function between contractible types is an equivalence.

```
contrEnds→isEquiv : isContr A → isContr B → (f : A → B) → isEquiv f
-- Exercise:
contrEnds→isEquiv c c' f = (inv→equiv f (λ _ → c .center) to-fro fro-to) .proof
  where
    to-fro : isSection f (λ _ → c .center)
    to-fro b = 
      f (c .center)   ≡⟨ sym (c' .contraction (f (c .center))) ⟩
      c' .center      ≡⟨ (c' .contraction) b ⟩
      b               ∎

    fro-to : isRetract f (λ _ → c .center)
    fro-to a = c .contraction a


contrExt : isContr A → isContr B → A ≃ B
-- Exercise:
contrExt c c' .map = (λ _ → (c' .center))
contrExt c c' .proof = contrEnds→isEquiv c c' (λ _ → (c' .center))
```

So, in fact, every contractible type is equivalent to ``⊤``.

```
isContr→≃⊤ : isContr A → A ≃ ⊤
isContr→≃⊤ c = contrExt c isContr-⊤
```

A map between propositions is not enough for them to be equivalent,
consider the unique map `∅ → ⊤`. But if there are maps both ways, then
that's enough. This is known as "proposition extensionality".

```
propExt : isProp A → isProp B
  → (f : A → B)
  → (g : B → A)
  → A ≃ B
-- Exercise:
propExt pA pB f g = inv→equiv f g (λ b → pB (f (g b)) b) (λ a → pA (g (f a)) a)
```

The converse of ``isContr→≃⊤`` is true: if `A` is equivalent to ``⊤``,
then `A` is contractible. To prove this, we will use an argument that
we will repeat, with variations, in a couple of other proofs.

Many properties of types are preserved by equivalences, but it turns
out that often just half of the data of an equivalence is enough.
Recall that a map *is* a retract when it *has* a section.

```
record _RetractOnto_ (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor retractOntoData
  field
    map : A → B
    section : SectionOf map

open _RetractOnto_ public
```

If `A` is equivalent to `B` then certainly `B` retracts onto `A`,
forgetting the other part of the equivalence.

```
equiv→retract : {A : Type ℓ} → {B : Type ℓ'} → (A ≃ B) → B RetractOnto A
equiv→retract e .map = e .proof .retract .map
equiv→retract e .section .map = e .map
equiv→retract e .section .proof = e .proof .retract .proof
```

If `B' retracts onto `A`, then in some sense `A` is a continuous
shrinking of `B`. And so if `B` is a proposition then `A` must be too.
Here is the key lemma, with a pre-drawn cube for your convenience:

                y — — — — — — — — > y
              / ^                 / ^
      .map  /   |            p  /   |
          /     |             /     |
        x — — — — — — — — > x       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |    r (s y)  — — — | — — > y
        |     /             |     /
        |   /               |   /
        | /                 | /
     r (s x) — — — — — — —  x

(Me)
                            ↓ refl
                      y — — — — — — — — > y
                    / ^                 / ^
             p →  /   |               / ←-|-- (A ∙∙ B ∙∙ C)
                /     |    ↓ refl   /     |
              x — — — — — — — — > x       |
              ^       |           ^       |                    ^   j
              |       | ← C       |refl → |                  k | /
              |       |    refl → |       |                    ∙ — >
              |       |           |       |                      i
    (sym A) → |    r (s y)  — — — | — — > y
              | B → /       ↑ C   |     /
              |   /               |   / ← (A ∙∙ B ∙∙ C)
              | /                 | /
          r (s x) — — — — — — —  x
                    ↑ (sym A)

where
  A = (sym (((r .section) .proof) x))
  B = ap (r .map) (ap (r .section .map) p)
  C = (((r .section) .proof) y)
(/Me)

                            ↓p    
                      x — — — — — — — — > y
                    / ^                 / ^
        (sym A) → /   |           C → /   |                
                /     |   ↓B        /     |
          r (s x) — — — — — — — > r (s y) |
              ^       |           ^       | ← C                ^   j
              |       | ← (sym A) |       |                  k | /
              |       |           |       |                    ∙ — >
              |       |     ↓ B   |       |                      i
       refl → | r (s x) — — — — — | — — > r (s y)
              |     /             |     /
              |   / ← refl refl → |   / ← refl
              | /                 | /
          r (s x) — — — — — — — r (s y)
                      ↑ B
                                   

```
retract-≡ : {ℓ₀ : Level} → {A B : Type ℓ₀} → (r : B RetractOnto A)
  → {x y : A}
  → (r .section .map x ≡ r .section .map y) RetractOnto (x ≡ y)
-- Exercise: (Hint: Using `∙∙` gives the cleanest argument!)
retract-≡ r {x} {y} .map q = (sym (((r .section) .proof) x)) ∙∙ (ap (λ a → r .map a) q) ∙∙ (((r .section) .proof) y)
  --                         x    ≡⟨ sym (((r .section) .proof) x) ⟩
  -- r .map (r .section .map x)   ≡⟨ ap (λ a → r .map a) q ⟩
  -- r .map (r .section .map y)   ≡⟨ ((r .section) .proof) y ⟩
  --                         y    ∎
retract-≡ r {x} {y} .section .map p = ap (λ a → r .section .map a) p
retract-≡ {A = A} {B = B} r {x} {y} .section .proof p i = Sq₀ (~ i)
  where
    pSymA = (((r .section) .proof) x)
    pB = ap (r .map) (ap (r .section .map) p)
    pC = (((r .section) .proof) y)

    Sq₁-faces : (i j k : I) → Partial (∂ i ∨ (~ j) ∨ (~ k)) A
    Sq₁-faces i j k (i = i0) = face j k
      where
        face : Square refl pSymA refl pSymA
        face j k = {!!}
    Sq₁-faces i j k (i = i1) = face j k
      where
        face : Square refl pC refl pC
        face j k = {!!}
    Sq₁-faces i j k (j = i0) = face i k
      where
        face : Square refl refl pB pB
        face j k = {!!}
    Sq₁-faces i j k (k = i0) = face i j
      where
        face : Square refl refl pB pB
        face i j = {!!}

    -- Sq₁ : Square pSymA pC pB p
    Sq₁ : Square pSymA pC pB (λ i → hcomp (∂ i ∨ ~ i1) (Sq₁-faces i i1))
    Sq₁ i j = hcomp (∂ i ∨ (~ j)) (Sq₁-faces i j)
    Sq₂ : Square pSymA pC pB p
    Sq₂ i j = {!Sq₁ (~ i) j !}

    Sq₀-faces : (i j k : I) → Partial ((~ i) ∨ ∂ j ∨ (~ k)) A
    Sq₀-faces i j k (i = i0) = face j k
      where
        face : Square pSymA pC (pSymA ∙∙ p ∙∙ (sym pC)) p
        face = {!!}
    Sq₀-faces i j k (j = i0) = face i k
      where
        face : Square pSymA refl pSymA refl
        face i k = pSymA (i ∨ k)
    Sq₀-faces i j k (j = i1) = face i k
      where
        face : Square pC refl pC refl
        face i k = pC (i ∨ k)
    Sq₀-faces i j k (k = i0) = face i j
      where
        face : Square (pSymA ∙∙ p ∙∙ (sym pC)) p pSymA pC
        face = {!!}

    Sq₀ : Square p ((sym pSymA) ∙∙ pB ∙∙ pC) refl refl
    Sq₀ i j = {!hcomp ((~ i) ∨ ∂ j) (Sq₀-faces i j)!}

    Sq₀c : Square p ((sym pSymA) ∙∙ pB ∙∙ pC) refl refl
    Sq₀c i j = {!hcomp ((~ i) ∨ ∂ j) (Sq₀-faces i j)!}
    -- Sq₀ : Square ((sym pSymA) ∙∙ pB ∙∙ pC) (λ i₁ → hcomp (~ i1 ∨ ∂ i₁) (Sq₀-faces i1 i₁)) refl refl
    -- Sq₀ i j = hcomp ((~ i) ∨ ∂ j) (Sq₀-faces i j)
```

Then the fact about ``isProp`` follows easily.

```
isProp-retract : B RetractOnto A → isProp B → isProp A
-- Exercise:
isProp-retract r pB x y = {!!}
```

In particular, any type equivalent to a proposition is also a
proposition.

```
isProp-equiv : A ≃ B → isProp B → isProp A
-- Exercise:
isProp-equiv = {!!}
```

And if some contractible type `B` retracts onto `A`, then `A` is also
contractible.

```
isContr-retract : B RetractOnto A → isContr B → isContr A
-- Exercise:
isContr-retract r c = {!!}

isContr-equiv : A ≃ B → isContr B → isContr A
-- Exercise:
isContr-equiv = {!!}
```

So we have a converse to ``isContr→≃⊤``, and being contractible is the
same as being equivalent to ``⊤``.

```
≃⊤→isContr : (A ≃ ⊤) → isContr A
-- Exercise:
≃⊤→isContr = {!!}
```


## Closure Properties of Propositions

Back in Lecture 1-5, we used ordinary type constructors to represent
logical operations on propositions. We had better make sure that our
new notion of proposition is preserved by these type constructors!

First, we have implication. If `A` and `B` are propositions then the
type of functions `A → B` is a proposition --- namely, the proposition
that `A` implies `B`.

```
isProp-→ : isProp B → isProp (A → B)
-- Exercise:
isProp-→ p f g i a = {!!}
```

As a special case of implication, we find that type negation `¬ A` is
always a proposition even when `A` isn't.

```
isProp-¬ : isProp (¬ A)
isProp-¬ = isProp-→ isProp-∅
```

If `B` is true, then `A → B` is always true. Using ``isContr`` as our
interpretation for "true proposition", this means that `A → B` is
contractible as soon as `B` is contractible.

```
isContr→ : isContr B → isContr (A → B)
-- Exercise:
isContr→ c = {!!}
```

The "and" of two propositions `A` and `B` is the type of pairs `A × B`.

```
isProp-× : isProp A → isProp B → isProp (A × B)
-- Exercise:
isProp-× pA pB = {!!}
```

And if `A` and `B` are both true, then `A × B` should also be true.

```
isContr-× : isContr A → isContr B → isContr (A × B)
-- Exercise:
isContr-× cA cB = {!!}
```

For contractibility, the converse of ``isContr-×`` holds: if the product
is contractible then the inputs must have been.

```
isContr-×-conv : isContr (A × B) → isContr A × isContr B
-- Exercise:
isContr-×-conv cAB = {!!}
```

The same is not true for propositions: a product of types being a
proposition does not imply that the two components are.

```
¬isProp-×-conv : ¬ ((A B : Type) → isProp (A × B) → isProp A × isProp B)
-- Exercise: (Hint: ``∅×≃∅``)
¬isProp-×-conv = {!!}
```

Propositions and contractible types are also closed under forming path
types. There's another way interpret this fact. The ``hcomp``
operation lets us fill in open boxes in any type. If the type is a
proposition, then we can fill any shape at all.


## Filling Shapes in Propositions

If a type is a proposition we can use the element of ``isProp`` to
find a path between any two points. But in fact more is true: that
path between the points is itself unique. All ways of connecting those
points by a path are equal.

This is a priori surprising: the definition of ``isProp`` gives us
paths between points, but says nothing about cubes of higher
dimension.

                          s
                b — — — — — — — — > d
              / ^                 / ^
         t  /   |            u  /   |
          /     |   r         /     |
        a — — — — — — — — > c       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       a — — — — — | — — > a
        |     /             |     /
        |   /               |   /
        | /                 | /
        a — — — — — — — — > a


```
isProp→Square : isProp A
  → {a b c d : A}
  → (r : a ≡ c) (s : b ≡ d)
  → (t : a ≡ b) (u : c ≡ d)
  → Square t u r s
-- Exercise: (Hint: Use `pA` to create each side.)
isProp→Square pA {a = a} r s t u i j = {!!}
```

An important special case of ``isProp→Square`` is when we fix two
sides of the square to be ``refl``, resulting in an ordinary path
between paths. There's another way to read this: for `x` and `y`
elements of a proposition, `x ≡ y` is also a proposition.

```
isProp→isProp≡ : isProp A → (x y : A) → isProp (x ≡ y)
-- Exercise:
isProp→isProp≡ = {!!}
```

And from this we get that the types of paths in any proposition are
always contractible.

```
isProp→isContr≡ : isProp A → (x y : A) → isContr (x ≡ y)
-- Exercise: 
isProp→isContr≡ p x y = {!!}
```

We could have used this as an alternative definition of what it means
to be a proposition, because it's trivial to go the other way:

```
isContr≡→isProp : ((x y : A) → isContr (x ≡ y)) → isProp A
-- Exercise: 
isContr≡→isProp f x y = {!!}
```

There's a another way we can generalise ``isProp``. If we have a path
of types where every type along the path is a proposition, we can
produce a path-over that path between any endpoints.

```
isProp→any-PathP : {A : I → Type ℓ}
  → ((i : I) → isProp (A i))
  → (a0 : A i0) (a1 : A i1)
  → PathP A a0 a1
-- Exercise: (Hint: `toPathP`)
isProp→any-PathP {A = A} hB a0 a1 = {!!}

isProp→isProp-PathP : {A : I → Type ℓ}
  → ((i : I) → isProp (A i))
  → (a0 : A i0) (a1 : A i1)
  → isProp (PathP A a0 a1)
-- Exercise: (Hint: Piggyback on `isProp→isProp≡`)
isProp→isProp-PathP pA x y = isProp-equiv {!!} {!!}
```

We can use what we've proven so far to bootstrap the process of
filling more interesting shapes. For example, any ``SquareP`` can be
filled. We write this out in full, painful generality, because we will
need to use it shortly.

```
isProp→any-SquareP : {A : I → I → Type ℓ}
  → ((i j : I) → isProp (A i j))
  
  → {a : A i0 i0} {b : A i0 i1} {c : A i1 i0} {d : A i1 i1}

  → (r : PathP (λ j → A j i0) a c) (s : PathP (λ j → A j i1) b d)
  → (t : PathP (λ j → A i0 j) a b) (u : PathP (λ j → A i1 j) c d)

  → SquareP A t u r s
-- Exercise:
isProp→any-SquareP pA r s t u = {!!}
```

We can prove similar facts for contractibility. These can be done
entirely by gluing together results we've already seen.

```
isContr→isContr≡ : isContr A → (a b : A) → isContr (a ≡ b)
-- Exercise: (Hint: `isProp-with-point→isContr`)
isContr→isContr≡ c a b = {!!}

isContr→isContr-PathP : {A : I → Type ℓ} (c : isContr (A i1)) → (a : A i0) → (b : A i1) → isContr (PathP A a b)
isContr→isContr-PathP {A = A} isc a b = isContr-equiv (PathP≃Path A) (isContr→isContr≡ isc _ _)
```

Let's give some more explicit examples of propositions. The first is a
little self-referential: for any type `A`, there is the proposition
that `A`... is a proposition.

```
isProp-isProp : isProp (isProp A)
-- Exercise:
isProp-isProp pA₀ pA₁ = {!!}
```

And `isContr A` is always a proposition; the proposition that `A` has
a unique element.

```
isProp-isContr : isProp (isContr A)
-- Exercise:
isProp-isContr cA₀ cA₁ = {!!}
```

There's another important type that is a proposition: the fact that a
map is an equivalence. This is surprisingly involved, so we will prove
it a little later in Lecture 2-9.


## Subtypes

Our definition of proposition leads to a good notion of "subtype". If
`P : A → Type` is a family of propositions depending on a type `A`,
then the *subtype* of `A` carved out by `P` is simply the type of
pairs `Σ[ a ∈ A ] P a`. So, an element of the subtype is pair `(a ,
p)` of an `a : A` and a witness `p : P a` that the proposition `P` is
true about `a`.

```
Even-subtype : Type
Even-subtype = Σ[ n ∈ ℕ ] isEvenP n

Zero-subtype : Type
Zero-subtype = Σ[ n ∈ ℕ ] (n ≡ℕ zero)
```

The main fact to prove about subtypes is that they have the same paths
as the types they came from. That is, `(a1 , b1) ≡ (a2 , b2)` is
equivalent to `a1 ≡ a2` whenever `B` is a family of propositions. 

```
≡-in-subtype : {A : Type ℓ} {B : A → Type ℓ'}
  → (p : (a : A) → isProp (B a))
  → (x y : Σ[ a ∈ A ] B a)
  → (x .fst ≡ y .fst) ≃ (x ≡ y)
≡-in-subtype pB x y = inv→equiv to (ap fst) to-fro fro-to
  where
    to : x .fst ≡ y .fst → x ≡ y
    -- Exercise: (Hint: `isProp→any-PathP`)
    to e = {!!}

    to-fro : isSection to (ap fst)
    -- Exercise: (Hint: `isProp→any-SquareP`)
    to-fro e = {!!}

    fro-to : isRetract to (ap fst)
    -- Exercise:
    fro-to p = {!!}
```

To foreshadow Lecture 3-1, this is extremely useful when we start
looking at algebraic structures such as groups, rings, and so on.
These come with some data, like addition and multiplication operators,
together with a bunch of axioms, like associativity, commutativity,
and so on. What we've just proven tells us that to build a path
between two groups, it's enough to build a path just between the
underlying data, ignoring all the axioms.


## Dependent Closure Properties

The ``isProp-×`` operation has an upgraded, dependent version. This
states that if `A` is a proposition and `P : A → Type` is a family of
propositions depending on `a : A` then the type of pairs `Σ[ a ∈ A ] B
a` is also a proposition. Really, `Σ[ a ∈ A ] P a` still represents
the proposition "`A` and `B`" --- the difference is that we can use it
in situations where the proposition `B` only makes sense when `A` is
known to hold.

```
isProp-Σ : {A : Type ℓ} {P : A → Type ℓ'}
  → isProp A
  → ((a : A) → isProp (P a))
  → isProp (Σ[ a ∈ A ] P a)
-- Exercise: (Hint: use ``isProp→any-PathP``.)
isProp-Σ pA pP (a₀ , b₀) (a₁ , b₁) i = {!!}
```

And similarly for contractibility. If `A` is contractible and `P : A →
Type` is a family of contractible types, then the entire Σ-type is
contractible. This is similar to the ``isContr-×`` case, but will
require ``isProp→any-PathP`` or ``transport-fixing`` in the second
component.

```
isContr-Σ : {P : A → Type ℓ} → isContr A → ((x : A) → isContr (P x)) → isContr (Σ[ a ∈ A ] P a)
isContr-Σ p q .center .fst = p .center 
isContr-Σ p q .center .snd = q (p .center) .center
isContr-Σ p q .contraction (a , b) i .fst = p .contraction a i 
isContr-Σ {P = P} p q .contraction (a , b) i .snd = q (p .contraction a i) .contraction (transport-fixing (λ j → P (p .contraction a (i ∨ ~ j))) i b) i
```

And ``isProp-→`` can be extended to dependent functions. If `P : A →
Type` is a family of propositions depending on `A`, then the type of
functions `(a : A) → P a` is a proposition; the proposition that "for
all `a : A`, the proposition `P a` holds".

```
isProp-Π : {A : Type ℓ} → {P : A → Type ℓ'}
  → (p : (a : A) → isProp (P a))
  → isProp ((a : A) → P a)
-- Exercise:
isProp-Π p f g = {!!}
```

And if in fact every `P a` does hold, then the "for all" proposition
holds too.

```
isContr-Π : {A : Type ℓ} → {P : A → Type ℓ'}
  → ((a : A) → isContr (P a))
  → isContr ((a : A) → P a)
-- Exercise:
isContr-Π c = {!!}
```


## Propositional Truncation

We are still missing two important logical operations, the same two
that we had trouble with back in Lecture 1-5: "or" and "exists".

Our guess for "or" was disjoint union ``⊎``, but the disjoint union of
two propositions is not necessarily a proposition. We checked in
``¬isProp-Bool`` that ``Bool`` is not a proposition, and we know from
``Bool≃⊤⊎⊤`` that ``Bool`` is the disjoint union `⊤ ⊎ ⊤`.

```
¬isProp-⊤⊎⊤ : ¬ isProp (⊤ ⊎ ⊤)
-- Exercise:
¬isProp-⊤⊎⊤ = {!!}
```

::: Aside:
But! If we know that the two propositions are mutually exclusive, then
their disjoint union is still a proposition.

```
isPropExclusive⊎ : isProp A → isProp B → ¬ (A × B) → isProp (A ⊎ B)
-- Exercise:
isPropExclusive⊎ pA pB dis x y = {!!}
```
:::

For "or" and "exists", we introduce another inductive type: the
*propositional truncation*. This accepts any type `A` as a parameter
and forms a proposition `∃ A` --- the proposition that "there exists
some element of A". An element of `∃ A` will be a proof that `A` has
some element, but crucially, knowing `∃ A` won't actually provide us
with a specific element of `A`, just the fuzzy knowledge that there
exists one.

```

data ∃_ (A : Type ℓ) : Type ℓ where
  in-∃ : A → ∃ A
  squash : (x y : ∃ A) → x ≡ y

infix 3 ∃_
```

The first constructor, written ``in-∃``, says that to prove that there
exists an element in `A`, it suffices to have an actual element of
`A`. The second constructor, ``squash``, is exactly the claim that `∃
A` to be a proposition. This is a recursive constructor (like ``suc``
is for ``ℕ``).

```
isProp-∃ : isProp (∃ A)
isProp-∃ = squash
```

::: Aside:
In fact, Agda would even let us declare the ``squash`` constructor to
have type `isProp (∃ A)`, and realise by unfolding the definition that
this is asking for a path constructor.
:::

::: Caution:
The usual terminology for propositional truncation in Homotopy Type
Theory is `∥ A ∥`, but this can get confusing if we are doing
mathematics where the same double-bars denote the norm of a vector or
operator.
:::

The recursion principle for `∃ A` says that to prove that `∃ A`
implies some proposition `P`, it suffices to assume we have an actual
element `a : A` and then prove `P`. That is, given a function `A → P`,
we can get an implication `∃ A → P` whenever `P` is a proposition.

```
∃-rec : (isProp P)
      → (A → P)
      → (∃ A → P)
-- Exercise: (Case-split, then use `pP` in the `squash` case.)
∃-rec pP f e = {!!}
```

::: Aside:
This definition is recursive --- we use ``∃-rec`` in its own
definition. It's tempting to give the ``squash`` constructor the
non-recursive type `(x y : A) → (in-∃ x) ≡ (in-∃ y)`. It turns out this is
not enough: it really is necessary to equate *all* elements of `∃ A`,
not just those coming from `A`. With the non-recursive type, it's not
possible to prove that `∃ A` is a proposition.
:::

As usual, there is a dependently-typed upgrade for this recursion
principle. The individual proposition `P` is replaced by a family of
types, each of which is a proposition.

```
∃-ind : {P : ∃ A → Type ℓ}
      → ((e : ∃ A) → isProp (P e))
      → ((a : A) → P (in-∃ a))
      → ((e : ∃ A) → P e)
-- Exercise: (Hint: `isProp→any-PathP`)
∃-ind pP f e = {!!}
```

In fact, all maps into a proposition are of this form, that is,
``∃-ind`` is an equivalence.

```
∃-ump-≃ : {P : ∃ A → Type ℓ}
      → ((e : ∃ A) → isProp (P e))
      → ((a : A) → P (in-∃ a))
      ≃ ((e : ∃ A) → P e)
-- Exercise:
∃-ump-≃ pP = propExt {!!} {!!} {!!} {!!}
```

``∃`` is functorial, that is, if we have a function from `A` to
`B` then `A` having an element implies `B` has an element.

```
∃-map : (A → B) → (∃ A → ∃ B)
-- Exercise:
∃-map f = {!!}
```

If `P` is already a proposition, truncating it should do nothing:

```
isProp→≃∃ : isProp P → P ≃ (∃ P)
-- Exercise: (Hint: use ``propExt``)
isProp→≃∃ isPropP = {!!}
```

In particular, truncating twice is the same as truncating once.

```
∃≃∃∃ : (∃ P) ≃ (∃ ∃ P)
∃≃∃∃ = isProp→≃∃ isProp-∃
```

With propositional truncation, we can finally define the proposition
representing "or" which has eluded us. The type `A ⊎ B` has some
element exactly when `A` has some element or `B` has some element.
Therefore, we can define `A orP B` as the proposition that there
exists an element in `A ⊎ B`.

```
_orP_ : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
A orP B = ∃ (A ⊎ B)
```

Here's how we can justify that this is the correct definition. First
of all, clearly `A orP B` is always a proposition, via ``isProp-∃``.
And, it has the correct universal mapping property with respect to
other propositions: `P orP Q → R` exactly when `P → R` and `Q → R`.

```
orP-ump-≃ : {P Q R : Type ℓ}
  → isProp P → isProp Q → isProp R
  → (P → R) × (Q → R) ≃ (P orP Q → R)
-- Exercise:
orP-ump-≃ pP pQ pR = {!!}
```
  

## References and Further Reading

* The original *[Homotopy Type Theory]* book:
  * Contractible Types: Chapter 3.11
  * Propositions: Chapter 3.3
  * Subtypes: Chapter 3.5
  * Propositional Truncation: Chapter 3.7
* Egbert Rijke's *[Introduction to Homotopy Type Theory]*:
  * Contractible Types: Chapter 10.1
  * Propositions: Chapter 12.1
  * Propositional Truncation: Chapter 14
* Martin Escardo's [Lecture Notes]:
  * [Contractible Types](https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#singleton-types)
  * [Propositions](https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#subsingleton-types)
  * [Propositional Truncation](https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#truncation) (using a different approach)

[Homotopy Type Theory]: https://homotopytypetheory.org/book/
[Introduction to Homotopy Type Theory]: https://arxiv.org/abs/2212.11082
[Lecture Notes]: https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/index.htmlure-Notes/HoTT-UF-Agda.html

* [The General Universal Property of the Propositional
  Truncation](https://arxiv.org/abs/1411.2682), Nicolai Kraus
