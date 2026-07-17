# GWB directed univalence: where a formalization attempt starts and stops

```rzk
#lang rzk-1
```

This probes whether the **Gratzer–Weinberger–Buchholtz** directed-univalence
results — the construction that would unblock the directed do-operator
(`causal-directed.rzk.md`) — could be formalized in rzk 0.8. The answer is
two steps in, then a research frontier.

## Step 1 — the universe of discrete types exists

The first object GWB need is the universe `𝒮` of **discrete** types: types whose
causal arrows are exactly their paths (`is-discrete`). It is a plain Σ-type and is
expressible directly:

```rzk
#def Discrete-Universe
  : U
  := Σ ( A : U) , ( is-discrete A)

#def underlying-type
  ( A : Discrete-Universe)
  : U
  := first A
```

## Step 2 — its directed univalence can be *stated*

GWB's theorem says that on `𝒮` the causal arrow type **is** the function type:
`hom 𝒮 A B ≃ (A → B)`. For `𝒮` to carry causal-arrow structure at all it must be
a directed ∞-category, `is-segal 𝒮`; granting that as a hypothesis, the
directed-univalence goal is expressible:

```rzk
#def gwb-directed-univalence-goal
  ( is-segal-𝒮 : is-segal Discrete-Universe)
  ( A B : Discrete-Universe)
  : U
  :=
    Equiv
      ( hom Discrete-Universe A B)
      ( underlying-type A → underlying-type B)
```

## …and there it blocks

`gwb-directed-univalence-goal` type-checks as a *statement* but is **not
inhabited**, and its hypothesis `is-segal Discrete-Universe` is **not provable**
here. Proving that the universe of discrete types is a directed ∞-category, and
that its arrows are the functions, is the GWB construction itself — carried out in
*triangulated / modal* type theory, with the Dedekind-cubical model where the
needed adjoints are sound. rzk 0.8 ships the modal substrate (experimental flat /
sharp / opposite, and it explicitly *disallows* the amazing right adjoint as
unsound in its standard model), but no directed-univalent universe is built on it,
and no formalization of GWB exists in any system. The only released directed-
univalence formalization is Weaver–Licata's *semantic* bicubical model, with the
cobar operator axiomatized — not a usable synthetic universe.

So a GWB formalization can **form** the universe of discrete types and **state**
its directed univalence — and stops at proving the universe is a directed
∞-category. That proof is the open frontier, on experimental tooling whose model
may not even match GWB's: a genuine research project, not an increment to this
development.
