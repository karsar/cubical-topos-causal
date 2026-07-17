# Directed companion (rzk)

An exploratory *directed* reformulation of the structural core of the causal
layer, in the simplicial type theory of Riehl and Shulman, using the
[rzk](https://github.com/rzk-lang/rzk) proof assistant on the
[sHoTT](https://github.com/rzk-lang/sHoTT) library.

Where the Agda development in `../src/` models causation with *symmetric*
identity types, this folder models causal influence as a **non-invertible**
directed arrow (`hom`) in a Segal type, so the asymmetry of causation is
primitive:

- a **causal world** is a Segal type; **causal influence** is a `hom` with no
  backward partner; **transitivity** of influence is Segal composition;
- a **mechanism** is a covariant family and **interventional propagation** is
  covariant transport; the trivial mechanism propagates a value unchanged, and a
  morphism of mechanisms commutes with propagation;
- in a **Rezk** world a variable is pinned down by the totality of its downstream
  effects (an identifiability statement of Yoneda type);
- a **counterfactual** is a twin network: two runs of the world sharing a single
  exogenous source.

## Scope and caveats

This development differs from the Agda part in `../src/`, and the differences are
deliberate:

- It is verified under **rzk 0.8**. The sHoTT library is pinned as a git
  submodule (`directed/sHoTT`, commit `5346e43`).
- Unlike the `--safe`, postulate-free Agda development, it **assumes one axiom**:
  extension extensionality (`extext : ExtExt`), the directed analogue of function
  extensionality, exactly as sHoTT itself uses.
- **Directed univalence** — and with it the **do-operator / intervention
  classifier** — is *stated but not inhabited*: it requires a directed-univalent
  universe, which no proof assistant currently provides. The structural laws
  above are proved; the intervention layer is future work.

## Typechecking

```
git clone --recursive https://github.com/karsar/cubical-topos-causal
cd cubical-topos-causal/directed
rzk typecheck
```

If you cloned without `--recursive`, fetch the submodule first with
`git submodule update --init`. The check loads sHoTT, `causal-directed.rzk.md`,
and `gwb-probe.rzk.md`, and reports `Everything is ok!`.
