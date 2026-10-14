# cubical-topos-causal

This repository is the Cubical Agda artifact for the paper
*"A cubical formalisation of topos causal models: intervention, forcing, and a contextuality obstruction."*

The paper describes the state at tag `v1.13-lmcs`. That tag extends the
earlier tag `v1.12-lmcs` (commit `9dd2a50`). It adds `SubModelArrow`,
which shows that the source's sub-model arrow cannot single out an
intervention over finite state spaces.  Tag `v1.12-lmcs` added the
identification, descent, local-reflection, groupoid-classicality and
topology-comparison results listed below.

The development has 62 modules in `src/Topos/` and 9 modules in
`src/Transport/`. They sit on a probability layer of 8 modules. The paper
uses 60 of the Topos modules and all 9 Transport modules. The two other
Topos modules, `VersionFactoring` and `VersionSite`, stay in the
repository, but the paper does not describe them.

The verified results include the following:

- The general subobject classifier, the classifier of a fixed value, and a
  classifier of admissible mechanisms on an exponential object.
- A comparison of intervention with conditioning at the level of kernels.
  A rational weight strictly between 0 and 1 shows that the two differ.
- The sub-model arrow. `SubModelArrow` works in the arrow category, where
  a model is a function from exogenous to endogenous states. Pearl's
  intervened model keeps the state spaces of its parent. When these are
  finite, every monic arrow from it into the parent is an isomorphism, by
  the pigeonhole principle. So the arrow only renames states, and the
  subobject it gives is the whole parent model. A perfectly confounded
  example shows the renaming. It also shows that the proper sub-model
  where X is true fixes Y, as conditioning does, while the intervention
  leaves Y free.
- Pullbacks and their universal property, presheaf forcing, and
  Lawvere–Tierney topologies. A pullback is a limit. It does not give the
  sheaf condition over a cover.
- Two topologies on the intervention site. `TopologyComparison` proves
  that double negation and the intervention topology agree on every
  decidable sieve. It also proves that they agree on all sieves exactly
  when double-negation elimination holds.
- Collider and mediator examples. In each, a support predicate does not
  persist under restriction. `SiteSelfObstruction` connects this failure to
  the probabilities of the confounded model. It also builds an internal
  truth value for the inequality between doing and seeing.
- Classicality. `Classicality` shows that internal validity is strictly
  stronger than validity over the covering family. `GroupoidClassicality`
  shows that the Boolean tautologies are forced exactly when every arrow
  of the base is invertible. This needs decidable atoms, and a base on
  which it is decidable whether an arrow has a section.
- Base change on sieves. Over posets, the back condition characterises the
  Heyting tier, which is the same as the injective tier. Local
  order-reflection within each principal downset gives the bijective tier.
  `AbstractionReflection` shows that global order-reflection is strictly
  stronger. It also shows that local reflection at a greatest context
  implies global reflection.
- Contextuality and holonomy examples. Synthetic count tables have no
  global table, and a comparison family is satisfiable.
- Identification. `Identification` proves that a correct strategy exists
  exactly when models with equal data agree on the query. It also proves
  four further facts:
  - A correct strategy is unique on realisable inputs.
  - Identifiability is equivalent to the truncated strategy type.
  - Identifiability persists when new data recover old data.
  - Strategies over a set of named interfaces form an h-set.
  `IdentificationModels` gives two acyclic structural causal models. They
  have equal observational joints and different values of the causal
  query. `IdentificationSieve` classifies the identifiability predicate
  that these two models determine. All claims in the example are relative
  to that declared class of two models. Its two interfaces are
  experimental datasets.
- Modal descent. `TransportDescent` proves a result for every base and
  every topology. A sieve is forced exactly when it is closed and its
  closure is forced. `TransportSoundness` applies this on the two-regime
  base. There the condition becomes double-negation closedness together
  with local truth. The empty sieve is closed but not forced, so the
  local-truth condition is necessary.

## Which modules the paper uses

| Modules | Count | Status |
|---|---|---|
| Core topos layer, including `AbstractionReflection`, `GroupoidClassicality` and `SubModelArrow` | 55 in `src/Topos/` | Paper |
| `IdentProbe`, `Identification`, `IdentificationModels`, `IdentificationSieve` | 4 | Paper. `IdentProbe` is an earlier, elementary probe |
| `TopologyComparison` | 1 | Paper |
| `Transport*`, including `TransportDescent` | 9 in `src/Transport/` | Paper |
| `VersionFactoring`, `VersionSite` | 2 | In the repository. The paper does not describe them |

The h-set theorem assumes that the interface names form a set. It does
not range over the universe of all h-sets. Strategies are defined only on
realisable datasets, because correctness says nothing about impossible
inputs. The paper states both conditions.

## Typechecking

All Agda sources are in `src/`. The file `cubical-topos-causal.agda-lib`
sets `include: src`. You need Agda 2.8.0 and version 0.9 of the cubical
library.

To typecheck the whole development, run this command from the repository
root:

```
agda --safe src/Everything.agda
```

`Everything.agda` imports every module. The development checks under
`--safe` with no postulates and no holes. The probability layer depends on
an ordered field, and the development supplies it concretely as ℚ.

Agda shows `UnsupportedIndexedMatch` warnings for some indexed pattern
matches. Such a definition does not compute when you apply it to a
transport. The warnings do not affect the safe-mode typecheck.

Every module declares `--safe` in its own options pragma. Thus the
artifact itself certifies safe mode, and the command-line flag is not
necessary for that.

The paper states one qualification, and this README states it the same
way. The distribution carrier `FDist` is a higher inductive type. One of
its path constructors, `mix-bayes-interchange`, is taken as primitive. It
is the Bayesian interchange law, and full conditioning needs it. It is an
open question whether it follows from the other constructors and the
arithmetic of the weights. The `--safe` flag does not decide this,
because a path constructor is part of a datatype declaration and is not a
postulate. The results that compute with distributions use this
constructor. The classifier, gluing, forcing and modal-closure layers are
statements about sieves, and they do not use it.

## Probability layer

The eight modules at the root of `src/` come from the companion artifact
[cubical-pearls](https://github.com/karsar/cubical-pearls)
(arXiv:2606.20351). They are `FDist-Convex`, `RuleDoCalc`, `Rule2` and the
`WeightQ` modules. This repository adds one interior weight,
`WeightQ.wHalf`, for the theorem that doing differs from seeing. Thus the
artifact checks on its own.

## Directed companion (rzk)

The `directed/` folder holds a separate, exploratory development in a
directed type theory. In it, causal influence is a non-invertible `hom` in
a Segal type. The development uses the
[rzk](https://github.com/rzk-lang/rzk) proof assistant and the
[sHoTT](https://github.com/rzk-lang/sHoTT) library. The library is a git
submodule. The development proves the structural laws of directed causal
reasoning: composition, covariant propagation, and Rezk and Yoneda
identifiability. It checks under rzk 0.8 and under rzk 0.11.3.

The directed companion has a different status from the Agda development.
The Agda development is `--safe` and has no postulates. The directed
companion assumes one axiom, extension extensionality. It states directed
univalence but does not prove it, so it states the do-operator but does
not construct it. See `directed/README.md`.
