# cubical-topos-causal

Cubical Agda artifact accompanying the paper
*"A cubical formalisation of topos causal models: intervention, forcing, and a contextuality obstruction."*

The artifact implements the 1-topos core of Mahadevan's topos causal
models. It has fifty-eight modules in `src/Topos/` and eight in
`src/Transport/`, over an eight-module probability layer. Not all of
them back the paper named above; see
[Which modules back which paper](#which-modules-back-which-paper).
The paper's own development is the fifty-four `src/Topos/` modules of
rows 1 and 3 of that table, together with the eight in
`src/Transport/`:

- the subobject classifier of sieves, with the value-fixing subobject
  `{x₀} ↪ X` as its characteristic map χ, and the classification
  theorem;
- the do-operator as model surgery on a confounder. It is
  machine-checked to differ from conditioning (`do ≠ see`), χ is its
  classifier, and a concrete interior witness inhabits the
  hypotheses, so the statement is not vacuous;
- collation of independent mechanisms as a pullback, with its
  universal property;
- the Kripke–Joyal internal language, which forces every connective
  and quantifier;
- a Lawvere–Tierney do-calculus. Inflationarity is derived from
  `j⊤ = ⊤` rather than assumed as a separate axiom, and the
  double-negation topology is an instance;
- a contextuality obstruction: pairwise-consistent data over three
  contexts with no global model, and a degree-1 holonomy class in
  that spirit;
- base change along a functor of regime categories (`BaseChange`,
  `BaseChangeClassifier`, `AbstractionTiers`, `TiersConverse`,
  `CoarseSite`, `CoarseClassicality`, `MergeAbstraction`,
  `HiddenRefinement`). Such a functor abstracts a site of causal
  contexts to a coarser one, and it induces a comparison map φB on
  truth values. For every functor, φB preserves ⊤, ⊥, ∧, ∨ and
  forcing, and it commutes with the classifier of a named
  intervention target. Over thin bases (posets), φB preserves ⇒ and
  ¬ exactly when the functor hides no refinement, and φB is
  surjective exactly when the functor conflates no alternatives.
  `MergeAbstraction` merges two interventions into one context and
  `HiddenRefinement` discards the interventional context, so each
  one fails a different condition;
- counterfactual transport (`src/Transport/`): the invariance of a
  counterfactual along an environment arrow, reusing the forcing and
  modal layers.

## Which modules back which paper

This repository has grown past the paper it was built for. Everything
below typechecks under `--safe` in the same build, but the modules
answer to different documents.

| Modules | Count | Backs |
|---|---|---|
| Core topos layer: classifier, `do` vs `see`, gluing, forcing, the modal layer, the intervention coverage, base change, the contextuality obstruction | 52 in `src/Topos/` | the paper named above |
| `Transport*` | 8 in `src/Transport/` | the paper named above, Section on counterfactual transport |
| `IdentProbe`, `IdentificationSieve` | 2 | the paper named above, section on the identification sieve |
| `AdjustmentSets`, `CyclicIdentification` | 2 | a follow-up on identification as a type. In preparation; nothing is published yet |
| `VersionFactoring`, `VersionSite` | 2 | not yet written up. They formalise VanderWeele and Hernan's treatment variation irrelevance as an internal truth value |

The last two rows are not cited by the paper and are not counted in
its module total. They are kept here because they build directly on
the same classifier and site infrastructure, and splitting them into
a separate repository would duplicate that base.

## Typechecking

All Agda sources live in `src/`. Run Agda from the repository root;
the `cubical-topos-causal.agda-lib` file sets `include: src`. You
need Agda 2.8.0 and the cubical library 0.9.

```
agda --safe src/Everything.agda
```

`Everything.agda` imports the whole development. It checks under
`--safe` with **zero postulates and zero holes**, and the ordered
field the probability layer depends on is realized concretely at ℚ.
Every module declares `--safe` in its own options pragma. The
artifact therefore certifies this itself and does not rely on the
flag being passed on the command line.

One qualification, stated the same way in the paper. The
distribution carrier `FDist` is a higher inductive type. One of its
path constructors, `mix-bayes-interchange`, is taken as primitive.
It is the Bayesian interchange law, and full conditioning needs it.
Whether it follows from the remaining constructors together with
the arithmetic of the weights is open, and `--safe` does not
adjudicate that, since a path constructor belongs to a datatype
declaration and is not a postulate. The results that compute with
distributions inherit the assumption. The classifier, gluing,
forcing and modal-closure layers are statements about sieves, and
they do not depend on it.

## Probability layer

The eight root modules in `src/` (`FDist-Convex`, `RuleDoCalc`,
`Rule2`, and the `WeightQ` modules) come from the companion artifact
[cubical-pearls](https://github.com/karsar/cubical-pearls)
(arXiv:2606.20351). One interior-weight witness (`WeightQ.wHalf`)
was added for the `do ≠ see` theorem, so the artifact checks on its
own.

## Directed companion (rzk)

The `directed/` folder holds a separate, exploratory development in
a *directed* type theory. It reads causal influence as a
non-invertible `hom` in a Segal type. It uses the
[rzk](https://github.com/rzk-lang/rzk) proof assistant on the
[sHoTT](https://github.com/rzk-lang/sHoTT) library, pinned as a
submodule. It proves the structural laws of directed causal
reasoning under **rzk 0.8**: composition, covariant propagation, and
Rezk/Yoneda identifiability.

The directed companion has a different status from the Agda
development above. The Agda part is `--safe` and postulate-free. The
directed companion **assumes one axiom**, extension extensionality.
Directed univalence is stated there but not yet inhabited, so the
do-operator is stated and not proved. See `directed/README.md`.
