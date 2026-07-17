# Directed causal models: causal influence as a non-invertible Segal `hom`

```rzk
#lang rzk-1
#assume extext : ExtExt
```

This is the **classical** directed seed: the directed-type-theoretic counterpart
of the topos paper's intervention/mechanism layer. The paper's Scope section
notes that a faithful *directed* treatment would model causal influence as a
**non-invertible arrow** (causation is asymmetric; the identity types of cubical
type theory are symmetric, so a path `x = y` silently yields `y = x`), and that
this is "not expressible in current Cubical Agda". It is expressible in released
**rzk 0.8 + sHoTT**, which is what this file realises and machine-checks. We work
in a **Segal type** `A` (a directed ∞-category) whose `hom A x y` are causal
arrows with composition but **no inverses**.

This is the classical structural core. The full **intervention / do-operator** via
*directed univalence* stays paper-level: it needs a directed-univalent universe
(and the modal layer rzk 0.8 newly ships), which is not yet built here — the block
this file reaches at the end.

## Causal worlds and influence

A **causal world** is a Segal type `A`: objects are variables or states, and a
causal arrow `X ⤳ Y` is an inhabitant of `hom A x y`. Causal influence is
**transitive** (Segal composition) and has no inverses.

```rzk
#def causal-influence
  ( A : U)
  ( x y : A)
  : U
  := hom A x y

#def influence-transitive
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : hom A x z
  := comp-is-segal A is-segal-A x y z f g
```

## Causal asymmetry: influence is not invertible

The directed primitive earns its keep here. A forward arrow `X ⤳ Y` yields **no**
backward arrow `Y ⤳ X`: in HoTT a path `x = y` gives `y = x` for free via `rev`,
but a directed `hom` gives nothing backward. A reverse causal link is therefore
**genuine extra data, supplied not derived**, and a two-way link is the
independent pairing of the two directions. This is exactly the asymmetry a
cubical path erases ("X causes Y" would collapse into "Y causes X"), and the
synthetic content the topos paper's Scope section points at.

```rzk
#def reverse-link
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : U
  := hom A y x

#def two-way-link
  ( A : U)
  ( x y : A)
  : U
  := Σ ( f : hom A x y) , ( hom A y x)
```

A variable trivially influences itself, and that self-influence composes to
itself — the degenerate causal loop, a theorem from the Segal left unit law.

```rzk
#def self-influence-degenerate
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x : A)
  : ( comp-is-segal A is-segal-A x x x ( id-hom A x) ( id-hom A x))
    =_{hom A x x} ( id-hom A x)
  := id-comp-is-segal A is-segal-A x x ( id-hom A x)
```

## Mechanisms and interventional propagation

A **mechanism** sends each variable to a value-space, with the downstream value
a functor of the upstream one: this is precisely a **covariant family**
`C : A → U`. Fixing a value at a cause and reading off the induced value at the
effect — the directed shadow of an intervention propagated along the structural
equations — is **covariant transport** along the causal arrow. The propagation
direction is built into the type: transport runs *forward* along causal arrows,
never backward, which is the mechanistic counterpart of the asymmetry above.

```rzk
#def mechanism
  ( A : U)
  : U
  := covariant-family A

#def propagate
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( u : C x)
  : C y
  := covariant-transport A x y f C is-covariant-C u
```

## Propagation is functorial: the trivial mechanism changes nothing

Propagating a value along the identity causal arrow — intervening through a
mechanism that does nothing — leaves the value unchanged. This is the unit law
of covariant transport, the directed shadow of the trivial conditional
independence `I(X:Y\|M)=0` in its degenerate case.

```rzk
#def propagate-trivial
  ( A : U)
  ( x : A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( u : C x)
  : ( propagate A x x ( id-hom A x) C is-covariant-C u) = u
  := id-arr-covariant-transport A x C is-covariant-C u
```

## Causal histories and the mediator chain rule

For a fixed source `a`, the family of causal influences *out of* `a` is `hom A a`,
a covariant family (representable). Propagating a history `e : hom A a x` along a
new arrow `f : X ⤳ Y` is exactly **post-composition** — extending the history by
one more causal step. (For the representable family, transport *is* composition,
definitionally.)

```rzk
#def causal-history
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  : mechanism A
  := ( hom A a , is-covariant-representable-is-segal A is-segal-A a)

#def propagate-history
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x y : A)
  ( f : hom A x y)
  ( e : hom A a x)
  : hom A a y
  :=
    covariant-transport A x y f ( hom A a)
      ( is-covariant-representable-is-segal A is-segal-A a) e

#def history-propagation-is-composition
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x y : A)
  ( f : hom A x y)
  ( e : hom A a x)
  : ( propagate-history A is-segal-A a x y f e)
    = ( comp-is-segal A is-segal-A a x y e f)
  := compute-covariant-transport-of-hom-family-is-segal A is-segal-A a x y e f
```

The **mediator chain rule**: propagating a history through a mediator `m` —
first `X ⤳ M`, then `M ⤳ Y` — equals propagating it along the composite causal
arrow `X ⤳ Y`. The cumulative causal effect factors through the mediator. This
is associativity of causal composition, and it is the directed counterpart of
mediator screening (the chain `X → M → Y`, where `M` screens `X` from `Y`).

```rzk
#def mediator-factorisation uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x m y : A)
  ( e : hom A a x)
  ( f : hom A x m)
  ( g : hom A m y)
  : ( propagate-history A is-segal-A a m y g
       ( propagate-history A is-segal-A a x m f e))
    = ( propagate-history A is-segal-A a x y
       ( comp-is-segal A is-segal-A x m y f g) e)
  := associative-is-segal extext A is-segal-A a x m y e f g
```

## Counterfactual twin networks

A counterfactual reasons about two worlds — factual and counterfactual — that
**share the same exogenous source**. Directedly this is a *span*: a shared
exogenous variable `u` with two causal arrows, one to the factual outcome and one
to the counterfactual. Sharing the source is built into the type, so the
counterfactual coherence — both worlds run on the same exogenous noise — is
structural, not an added constraint.

```rzk
#def twin-network
  ( A : U)
  ( u xf xc : A)
  : U
  := Σ ( _ : hom A u xf) , ( hom A u xc)
```

Given a mechanism and a value of the shared exogenous, propagating along the two
arms yields the factual and counterfactual outcomes together — Pearl's abduction
(fix the exogenous) followed by the two predictions. Both arms run on the *same*
exogenous value `e`, the twin network's shared-source constraint.

```rzk
#def twin-propagate
  ( A : U)
  ( u xf xc : A)
  ( tw : twin-network A u xf xc)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( e : C u)
  : Σ ( _ : C xf) , ( C xc)
  :=
    ( propagate A u xf ( first tw) C is-covariant-C e
    , propagate A u xc ( second tw) C is-covariant-C e)
```

This is the span formulation — the shared exogenous as common cause, faithful to
Pearl's twin network. The dual cospan *pullback* (gluing mechanisms over a shared
overlap, as in the undirected paper's sheaf gluing) is reachable through sHoTT's
limit API at the cost of the cone/finality plumbing.

## Downstream determination (directed identifiability)

The Yoneda embedding sends a causal link `a' ⤳ a` to the natural transformation
of downstream-influence cones it induces. In a Rezk (complete) causal world it is
fully faithful, so a variable is determined by *how it influences everything
downstream* — the directed shadow of identifiability from the downstream cone.

```rzk
#def downstream-influence
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a a' : A)
  : hom A a' a → ( z : A) → hom A a z → hom A a' z
  := yoneda-embedding A is-segal-A a a'
```

## Mechanisms transform naturally with intervention

A morphism of mechanisms `φ : C ⇒ D` (a fiberwise map of value-spaces) **commutes
with interventional propagation**: transforming a value then propagating it equals
propagating then transforming. This is the directed naturality of interventions —
a structure-preserving map of mechanisms respects every `do`.

```rzk
#def mechanism-morphism-respects-propagation
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C D : A → U)
  ( is-covariant-C : is-covariant A C)
  ( is-covariant-D : is-covariant A D)
  ( φ : ( z : A) → C z → D z)
  ( u : C x)
  : ( propagate A x y f D is-covariant-D ( φ x u))
    = ( φ y ( propagate A x y f C is-covariant-C u))
  :=
    naturality-covariant-fiberwise-transformation
      A x y f C D is-covariant-C is-covariant-D φ u
```

## Causal identity is causal isomorphism

A **causal isomorphism** between variables is an invertible causal arrow. In a
**Rezk** (complete) causal world, the identity of variables is *equivalent* to
causal isomorphism: two variables are equal exactly when causally isomorphic.
This is a genuinely directed identifiability — the isomorphism is built from
directed `hom`s, so "same variable" means "same incoming and outgoing causal
role". A symmetric (path) account cannot state it, because there identity is
already symmetric and the directed roles have been collapsed.

```rzk
#def causal-isomorphism
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  : U
  := Iso A is-segal-A x y

#def causal-identity-is-causal-iso
  ( A : U)
  ( is-rezk-A : is-rezk A)
  ( x y : A)
  : is-equiv ( x = y) ( Iso A ( first is-rezk-A) x y) ( iso-eq A ( first is-rezk-A) x y)
  := ( second is-rezk-A) x y
```

## Where the development blocks: the do-operator

Everything above — causal influence, its non-invertibility, transitivity,
mechanisms as covariant families, forward propagation, the mediator chain rule,
downstream determination — is machine-checked in released rzk 0.8 + sHoTT, with
no modal layer and no universe machinery.

The block is the **do-operator** itself. An intervention `do(X := x₀)` mutilates
the causal world: it severs `X`'s incoming influences and replaces its mechanism
by a constant. As an operation it lives on the *universe* of causal worlds (or of
value-types), and the topos-paper account extracts it as a **morphism in a
directed-univalent universe** via directed univalence, `hom 𝒰(A,B) ≃ (A → B)`.
That universe and its directed univalence are **not available in rzk**: rzk 0.8
ships an experimental flat/sharp/opposite modal layer (the prerequisite the
Gratzer–Weinberger–Buchholtz construction needs), but no directed-univalent
universe is built on it, and those results remain paper-only. So the intervention
layer stays paper-level — exactly the boundary the topos paper's Scope section
states, here reached concretely from the directed side.

The Gratzer–Weinberger–Buchholtz directed-univalence theorem is what would
unblock it: for **discrete** types, the causal arrow type is the function type.
We can *state* the goal in rzk —

```rzk
#def directed-univalence-statement
  ( A B : U)
  ( is-discrete-A : is-discrete A)
  ( is-discrete-B : is-discrete B)
  : U
  := Equiv ( hom U A B) ( A → B)
```

— but we cannot inhabit it. A proof needs the universe `U` itself to be a
directed-univalent ∞-category (`is-segal U` plus the univalence), the object
Gratzer–Weinberger–Buchholtz construct in triangulated/modal type theory. rzk
0.8's experimental modal layer is the substrate that construction needs, but the
universe is not built on it, and the result is paper-only. So the directed
account can *name* its own missing piece, and there it stops.

## Summary: what the directed account keeps that the symmetric one cannot

The cubical (undirected) development machine-checks the *full* 1-topos
do-calculus and transportability, but represents causal arrows as invertible
paths, erasing the asymmetry of causation. This directed development keeps that
asymmetry faithfully — a causal arrow yields nothing backward — and
machine-checks the structural layer (influence, transitivity, mechanisms,
propagation, the mediator chain rule, downstream determination) in released rzk.
The two meet at a clean boundary: the do-operator, which the undirected account
checks in full and the directed account can only state, pending a
directed-univalent universe.
```
