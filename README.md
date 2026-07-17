# cubical-topos-causal

Cubical Agda artifact accompanying the paper
*"A cubical formalisation of topos causal models: intervention, sheaf gluing, and the intuitionistic do-calculus."*

The artifact implements the 1-topos core of Mahadevan's topos causal models —
thirty modules in `src/Topos/`, over an eight-module probability layer:

- the subobject classifier of sieves, with the intervention `do(X := x₀)` as its
  characteristic map and the classification theorem;
- sheaf gluing of independent mechanisms, as a pullback with its universal property;
- the Kripke–Joyal internal language, forcing every connective and quantifier;
- a Lawvere–Tierney do-calculus, with the inflationarity axiom (missing from the
  usual three) restored and the double-negation topology as a concrete instance;
- a contextuality obstruction — pairwise-consistent data over three contexts with
  no global model — and its first Čech cohomology class.

## Typechecking

All Agda sources live in `src/`; run Agda from the repository root (the
`cubical-topos-causal.agda-lib` sets `include: src`). You need Agda 2.8.0 and the
cubical library 0.9.

```
agda --safe src/Everything.agda
```

`Everything.agda` imports the whole development; it checks under `--safe` with
**zero postulates and zero holes**, and the ordered field the probability layer
depends on is realized concretely at ℚ.

## Probability layer

The eight root modules in `src/` (`FDist-Convex`, `RuleDoCalc`, `Rule2`, and the
`WeightQ` modules) are reused unchanged from the companion artifact
[cubical-pearls](https://github.com/karsar/cubical-pearls) (arXiv:2606.20351), so
the artifact checks on its own.

## Directed companion (rzk)

The `directed/` folder holds a separate, exploratory development in a *directed*
type theory: causal influence as a non-invertible `hom` in a Segal type, in the
[rzk](https://github.com/rzk-lang/rzk) proof assistant on the
[sHoTT](https://github.com/rzk-lang/sHoTT) library (pinned as a submodule). It
proves the structural laws of directed causal reasoning — composition,
covariant propagation, Rezk/Yoneda identifiability — under **rzk 0.8**.

It sits on a different footing from the Agda development above: unlike the
`--safe`, postulate-free Agda part, the directed companion **assumes one axiom**
(extension extensionality), and directed univalence — hence the do-operator — is
stated but not yet inhabited. See `directed/README.md`.
