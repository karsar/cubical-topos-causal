# Directed companion (rzk)

This folder holds an exploratory directed version of the structural core of
the causal layer. It uses the simplicial type theory of Riehl and Shulman.
The proof assistant is [rzk](https://github.com/rzk-lang/rzk), and the
library is [sHoTT](https://github.com/rzk-lang/sHoTT).

The Agda development in `../src/` represents direction with explicit
categories, because its identity types are symmetric. In this folder, causal
influence is a non-invertible directed arrow (`hom`) in a Segal type. Thus
the asymmetry of causation is part of the type theory. The dictionary is as
follows:

- A causal world is a Segal type. Causal influence is a `hom` with no
  backward partner. Transitivity of influence is Segal composition.
- A mechanism is a covariant family. Interventional propagation is covariant
  transport. The trivial mechanism propagates a value unchanged. A morphism
  of mechanisms commutes with propagation.
- In a Rezk world, the totality of its downstream effects determines a
  variable. This is an identifiability statement of Yoneda type.
- A counterfactual is a twin network. A twin network is two runs of the
  world that share one exogenous source.

## Scope and limits

This development differs from the Agda development in `../src/` in three
ways:

- It checks under rzk 0.8 and under rzk 0.11.3. The sHoTT library is a git
  submodule (`directed/sHoTT`, commit `5346e43`).
- It assumes one axiom, extension extensionality (`extext : ExtExt`). This
  axiom is the directed analogue of function extensionality, and sHoTT uses
  it in the same way. The Agda development is `--safe` and has no postulates.
- It states directed univalence but does not prove it. Thus the do-operator,
  which is the intervention classifier, is also stated and not constructed.
  The construction needs a directed-univalent universe, and no released proof
  assistant provides one yet. The structural laws above are proved. The
  intervention layer is future work.

## Typechecking

To typecheck the development, run these commands:

```
git clone --recursive https://github.com/karsar/cubical-topos-causal
cd cubical-topos-causal/directed
rzk typecheck
```

If you cloned without `--recursive`, get the submodule first with
`git submodule update --init`. The check loads sHoTT,
`causal-directed.rzk.md` and `gwb-probe.rzk.md`. It reports
`Everything is ok!`.
