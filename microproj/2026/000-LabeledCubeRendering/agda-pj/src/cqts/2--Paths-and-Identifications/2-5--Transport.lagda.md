<!--
```
module 2--Paths-and-Identifications.2-5--Transport where

open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 1--Type-Theory.1-5--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling

private
  variable
    ℓ ℓ' : Level
    A A' B C : Type ℓ
    x y : A
```
-->


# Lecture 2-5: Transport

In this lecture, we will revisit ``transport`` and ``subst``, the
operations that let us move terms along a path between types.

The fundamental underlying operation is the slightly-more-general
``transport-fixing``, and understanding this will make use of the
intuition for partial elements that we developed in the previous
lecture.


## Transport Fixing a Formula

Here is the actual definition of ``transport`` which we vskipped when
we first saw it in Lecture 2-3.

```
transport-again : {A B : Type ℓ} → A ≡ B → A → B
transport-again p a = transport-fixing (λ i → p i) i0 a
```

This uses the built-in ``transport-fixing`` operation which has type

```
_ = {ℓ : Level} → (A : (i : I) → Type ℓ) → (φ : I) → A i0 → A i1
```

So, the ``transport-fixing`` operation takes in three arguments:

* `A : I → Type ℓ` is a path of types,
* `φ : I` is a formula, and,
* `a : A i0` is an element of the type at the start of the line `A`,

and the result is an element of the type `A i1` at the other end of
the path.

As usual, to understand the purpose of `φ`, we need to imagine we are
in the context of some other cubical variables. The purpose of the
formula `φ` is to specify parts of the cube *where the transport is
constant*. So `transport p x = transport-fixing (λ i → p i) i0 x` is
not constant anywhere, but `transport-fixing (λ _ → A) i1 x` is
constant everywhere and so is identical to `x`.

```
_ = λ {ℓ : Level} {A : Type ℓ} (a : A)
  → test-identical (transport-fixing (λ _ → A) i1 a) a
```

Agda will give an error if you demand ``transport-fixing`` be constant
in a way that doesn't make sense, like claiming that our original
definition of ``transport`` is constant everywhere:

```
-- Fails!
-- bad-transport-fixing : {A B : Type ℓ} → A ≡ B → A → B
-- bad-transport-fixing p a = transport-fixing (λ i → p i) i1 a
```

Here's an application. When ``transport``ed along `p`, the element `a
: A` becomes the element `transport p a : B`. It seems reasonable for
there to be a ``PathP`` over `p` connecting `a` and `transport p a`
We can use ``transport-fixing`` to construct one:

```
transport-filler : (p : A ≡ B) (a : A)
  → PathP (λ i → p i) a (transport p a)
transport-filler p a i = transport-fixing (λ j → p (i ∧ j)) (~ i) a
```

Let's check why the endpoints of this ``PathP`` are correct.

* When `i = i0`, the ``transport-fixing`` should give back `a`,
  because we've claimed that transport should be constant when `~ i`
  holds. In this case, the type is `(λ j → p (i0 ∧ j)) = (λ j → p i0)`
  which is constant at `A`, which is indeed the type of `a`.

* When `i = i1`, we have `~ i = i0` and `p (i1 ∧ j) = p j`, so that
  `transport-filler p a i1 = transport-fixing (λ j → p j) i0 a`. This
  is is exactly the definition of `transport p a`.

Of course, this helper specialises to ``subst``, which is a particular
instance of ``transport``.

```
subst-filler : (B : A → Type ℓ) (p : x ≡ y) → (b : B x)
  → PathP (λ i → B (p i)) b (subst B p b)
subst-filler B p = transport-filler (λ i → B (p i))
```

Try using ``transport-fixing`` to prove that that transporting an element
`x : A` along the constant path of types at `A` gives back `x`.

```
transport-refl : (a : A) → transport (λ i → A) a ≡ a
-- Exercise:
transport-refl {A = A} a i = transport-filler (λ j → A) a (~ i)
```

An important application of ``transport-fixing`` is showing that
``transport`` is invertible. 

```
transport-cancel : (p : A ≡ B) (b : B)
  → transport (λ i → p i) (transport (λ i → sym p i) b) ≡ b
```

Here's a hint. Unfolding the definition of ``transport``, the type of
the left endpoint of that path is

    transport-fixing (λ i → p i) i0 (transport-fixing (λ i → p (~ i)) i0 b)

which you can verify by hitting `C-c C-,`. So, our goal is to engineer
an expression also involving an interval variable `j` which reduces to
this large expression when `j = i0` and which simplifies to just `b`
when `j = i1`. For the latter, remember that the whole point of
``transport-fixing`` is that `transport-fixing (λ _ → A) i1 x`
computes to exactly `x`, so `b` is the same as:

    transport-fixing (λ i → p ?) i1 (transport-fixing (λ i → p ?) i1 b)

```
-- Exercise:
-- transport-cancel : (p : A ≡ B) (b : B)
--   → transport (λ i → p i) (transport (λ i → sym p i) b) ≡ b
transport-cancel p b j = transport-fixing (λ i → p ((i ∨ j))) j (transport-fixing (λ i → p (~ i ∨ j)) j b)
-- transport-cancel p b j = {!transport-fixing (λ i → p ((~ i ∧ j) ∨ i)) (j) (transport-fixing (λ i → p (j ∨ ~ i)) (j) b)!}
```

With ``transport-cancel`` in hand, we can show that `transport p` is
an equivalence of types with inverse `transport (sym p)`.

```
path→equiv : A ≡ B → A ≃ B
-- ExercisE:
-- path→equiv p = inv→equiv (transport p) {!!} {!!} {!!}
path→equiv p = inv→equiv (transport p) (transport (sym p))
                         (transport-cancel p) (transport-cancel (sym p))
```

And with a little effort, we can show that the equivalence that
results when ``path→equiv`` is supplied ``refl`` is equal to the
``idEquiv`` from earlier. This can be done with several uses of
``transport-refl``, or you can use ``transport-fixing`` directly.

```
path→equiv-refl : path→equiv refl ≡ idEquiv A
-- Exercise: (Hint: Use a couple of connection squares!)
path→equiv-refl i .map a = transport-refl a i
path→equiv-refl i .proof .section .map a = transport-refl a i
path→equiv-refl i .proof .section .proof a j = transport-cancel refl a (i ∨ j)
path→equiv-refl i .proof .retract .map a = transport-refl a i
path→equiv-refl i .proof .retract .proof a j = transport-cancel refl a (i ∨ j)

-- path→equiv-refl i .map a = transport-fixing (λ j → refl j) i a
-- path→equiv-refl i .proof .section .map a = transport-fixing (λ j → refl j) i a
-- path→equiv-refl i .proof .section .proof a = transport-cancel refl a
-- path→equiv-refl i .proof .retract .map a = transport-fixing (λ j → refl j) i a
-- path→equiv-refl i .proof .retract .proof a j = transport-cancel refl a (i ∨ j)
```


## Converting Between PathP and Path

There is a second way that ``PathP`` and ``transport`` relate. Recall
that an element of `PathP A a₀ a₁` connects two elements `a₀ : A i0`
and `a₁ : A i1` of types at either end of a line `A : I → Type`, so
bthat the type is allowed to vary as we travel from `a₀` to `a₁`.

Instead of travelling along the line `A`, we could first transport the
endpoint `a₀` over to the type `A i1`, and then ask for an ordinary
path that lives entirely inside `A i1`. That is, a ``PathP`` is
equivalent to ``Path`` involving a transport, and vice versa.

For the first conversion, ``toPathP``, we need to do an ``hcomp``.

      a₀ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ > a₁
       ^                    ^
    a₀ |                    | p                    ^
       |                    |                    j |
      a₀ — — — > transport (λ j → A j) a₀          ∙ — >
                                                     i
                A i
     A i0 — — — — — — — — > A i1

```
toPathP : {A : I → Type ℓ} {a₀ : A i0} {a₁ : A i1}
  → Path (A i1) (transport (λ j → A j) a₀) a₁
  → PathP A a₀ a₁
toPathP {A = A} {a₀} {a₁} p i
  = hcomp (∂ i) (λ j → λ 
    { (i = i0) → a₀
    ; (i = i1) → p j 
    ; (j = i0) → transport-filler (λ j → A j) a₀ i })
```

To go back the other way, we will use ``transport-fixing`` again, but
in a new way. When `i = i0` we want `fromPathP p i0 = transport (λ i →
B i) b1` and when `i = i1` we want `fromPathP p i1 = b2`. So we will
ask for ``transport-fixing`` to be constant when `i = i1`.

```
fromPathP : {A : I → Type ℓ} {a₀ : A i0} {a₁ : A i1}
  → PathP A a₀ a₁
  → Path (A i1) (transport (λ j → A j) a₀) a₁
fromPathP {A = A} p i = transport-fixing (λ j → A (i ∨ j)) i (p i)
```

These two maps are inverses. Unfortunately, this is a real pain to
show directly, involving some gnarly ``hcomp``s. So, we will cheat,
and produce an equivalence using the ``path→equiv`` function we just
defined.

```
PathP≡Path : (A : I → Type ℓ) {a₀ : A i0} {a₁ : A i1}
  → PathP A a₀ a₁ ≡ Path (A i1) (transport (λ i → A i) a₀) a₁
PathP≡Path A {a₀} {a₁} i =
  PathP (λ j → A (i ∨ j)) (transport-filler (λ j → A j) a₀ i) a₁

PathP≃Path : (A : I → Type ℓ) {a₀ : A i0} {a₁ : A i1}
  → (PathP A a₀ a₁) ≃ (transport (λ i → A i) a₀ ≡ a₁)
PathP≃Path A = path→equiv (PathP≡Path A)
```

This certainly gives an equivalence, but the forward and backward maps
are not the nice ``toPathP`` and ``fromPathP`` maps that we
defined above. For our purposes, this simpler equivalence is good
enough.


## Transport Computes

``transport-fixing`` (and therefore ``transport`` and ``subst``) come
with some magic that cause it to simplify when more information is
known about the line of types `A`.

When the path of types is constant at an inductive type such as ``ℕ``
or ``Bool``, then transporting along does nothing, and the transport
vanishes.

```
_ = λ (x : ⊤)    → test-identical (transport (λ i → ⊤)    x) x
_ = λ (x : Bool) → test-identical (transport (λ i → Bool) x) x
_ = λ (x : ℕ)    → test-identical (transport (λ i → ℕ)    x) x
```

If we don't know anything about the type, however, transporting over a
constant path is not by definition the identity. 

```
{- Error!
_ = λ (A : Type) (x : A) → test-identical (transport (λ i → A) x) x
-}
```

::: Aside:
It is unfortunate that this doesn't work in general. In the study of
cubical type theories, this property is called *regularity*. It's not
currently known whether a there is a version of cubical type theory
that supports regularity, higher types (discussed shortly) and
desirable properties like canonicity. Right now, it seems that at
least one of these things has to give.
:::

For the basic type formers that we have seen (pairs, functions,
paths), ``transport`` computes to some combination of ``transport``s
involving the input types.

```
module _ {A : I → Type} {B : I → Type} where private
```

To transport in a type of pairs, we just transport in each component:

```
  _ = λ {x : A i0} {y : B i0} → test-identical
      (transport (λ i → A i × B i) (x , y))
      (transport (λ i → A i) x , transport (λ i → B i) y)
```

To transport in a type of functions, we transport *backwards* along
the domain, apply the function, and then transport forwards along the
codomain:

```
  _ = λ {f : A i0 → B i0} → test-identical
      (transport (λ i → A i → B i) f)
      (λ x → transport (λ i → B i) (f (transport (λ i → A (~ i)) x)))
```

This is the only way this could fit together, because the input has
type `f : A i0 → B i0`, but `transport (λ i → A i → B i) f` needs to
be a function `A i1 → B i1`. To apply `f` to an element of `A i1`, we
first need to pull it back to an element of `A i0`.

``transport`` in a type of paths becomes a (double) composition. For a
path `a₀ ≡ a₁`, the transport is the top of the following square:


              a₀ i1 ∙ ∙ ∙ ∙ ∙ ∙ > a₁ i1
                ^                   ^               ^    
                |                   |             j |    
                |                   |               ∙ — >
          tr A (a₀ i0) — — — > tr A (a₁ i0)           i  
                                               
The left and right sides can be produced by ``fromPathP``. And on the
bottom, we have exactly ``ap`` of ``transport`` on the original path.
That transport on the bottom is now happening in `A`, and so the
``transport`` can continue to compute depending on what `A` is.

::: Aside:
In fact, this transport is one way to justify introducing ``hcomp`` in
the first place. Without it, what is ``transport`` in a path type
supposed to be?
:::

```
module _ {A : I → Type}
         {a₀ : (i : I) → A i}
         {a₁ : (i : I) → A i}
         {p : a₀ i0 ≡ a₁ i0}
  where
  _ = test-identical
      (transport (λ i → a₀ i ≡ a₁ i) p)
      -- Exercise:
      ((λ i → fromPathP (λ j → a₀ j) (~ i)) 
       ∙∙ (λ i → transport-fixing (λ j → A j) i0 (p i)) 
       ∙∙ λ i → fromPathP (λ j → a₁ j) i)
  
```

``PathP`` is similar but we have to write the ``hcomp`` manually,
because we only defined ``∙∙`` for ordinary paths.

```
module _ {A : I → I → Type}
         {a₀ : (i : I) → A i i0}
         {a₁ : (i : I) → A i i1}
         {p : PathP (A i0) (a₀ i0) (a₁ i0)}
  where
  _ = test-identical
      (transport (λ i → PathP (A i) (a₀ i) (a₁ i)) p)
      (λ j → hcomp (∂ j) (λ i → λ { (j = i0) → fromPathP (λ i → a₀ i) i;
                                    (j = i1) → fromPathP (λ i → a₁ i) i;
                                    (i = i0) → transport (λ i → A i j) (p j) } ))
```

We can mix and match these. Here is how a "`B`-valued binary operation
on `A`" would transport. This just decomposes into transport
(backwards) in the pair, followed by application of the function, then
transport forwards of the result:

```
module _ {A : I → Type} {B : I → Type} where
  _ = λ {m : A i0 × A i0 → B i0} → test-identical
      (transport (λ i → A i × A i → B i) m)
      (λ (x , y) →
        transport (λ i → B i) (m (transport (λ i → A (~ i)) x , 
                                  transport (λ i → A (~ i)) y)))
```

And here's how a function into ``Bool`` transports. As we have seen,
transport in ``Bool`` disappears, so in fact the result only contains
a (backwards) transport applied to the input.


```
  _ = λ {p : A i0 → Bool} → test-identical
    (transport (λ i → A i → Bool) p)
    (λ x → p (transport (λ i → A (~ i)) x))
```

Try it yourself:

```
  _ = λ {m : A i0 × A i0 → A i0} → test-identical
    (transport (λ i → A i × A i → A i) m)
    -- Exercise:
    λ (x , y) → transport (λ i → A i) 
      (m ((transport (λ i → A (~ i)) x) , 
          (transport (λ i → A (~ i)) y)))

  _ = λ {y : (A i0 → A i0) → A i0} → test-identical
    (transport (λ i → (A i → A i) → A i) y)
    -- Exercise:
    λ f → transport (λ i → A i) (y (λ x → transport (λ i → A (~ i)) 
          (f (transport (λ i → A i) x)) ))


  -- Me
  -- It doesn't work without application:
  -- _ = test-identical
  --   (transport (λ i → A i × B i))
  --   (transport (λ i → A i) , transport (λ i → B i))
```

## References and Further Reading

These use a different notion of path, but many properties are similar.
* The original *[Homotopy Type Theory]* book:
  * Transport: Chapter 2.3
* Egbert Rijke's *[Introduction to Homotopy Type Theory]*:
  * Transport: Chapter 5.4

[Homotopy Type Theory]: https://homotopytypetheory.org/book/
[Introduction to Homotopy Type Theory]: https://arxiv.org/abs/2212.11082

* Agda Documentation
  * [Transport](https://agda.readthedocs.io/en/latest/language/cubical.html#transport)
* HoTTEST Summer School 2022
  * [Transport](https://github.com/martinescardo/HoTTEST-Summer-School/blob/main/Agda/Cubical/Lecture8-notes.lagda.md)
* Tutorial for `cubicaltt`, an early cubical proof assistant
  * [Transport](https://github.com/mortberg/cubicaltt/blob/master/lectures/lecture3.ctt)


Regularity
https://arxiv.org/pdf/1808.00920
