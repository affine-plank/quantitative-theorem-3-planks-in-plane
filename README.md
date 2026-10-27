# Quantitative affine plank inequalities

**[Theorems and definitions](QuantitativePlanks.lean)** ·
[Proof](QuantitativePlanks/Proof.lean) · [Verification](verification/README.md)

Lean 4 proofs of the Affine Plank Conjecture (APC) for three planks in the
plane and its sharp quantitative extension (QAPC). The library also proves
QAPC for two planks in every positive dimension.

For a convex body `K` and planks with total relative width `R`, QAPC asserts

$$
\operatorname{vol}(K\setminus\bigcup_i P_i)
\;\ge\;\max(0,1-R)^d\operatorname{vol}(K).
$$

Relative width is plank width divided by the width of `K` in the same direction.
The planar result has `d = 2`. The arbitrary-number, arbitrary-dimensional
conjecture remains open; conditional general lemmas state their hypotheses.

## Read the proof

The main file defines a plank as a nonconstant affine function and states the
three theorems. It includes nonclosed and unbounded convex sets. `Point 2`
means the plane; `relativeWidth` and volume allow infinite values.

* [QuantitativePlanks/Proof.lean](QuantitativePlanks/Proof.lean): the compact proof, from APC to QAPC.
* `Plank/` and `ResearchFormalized/`: reusable geometry and standard mathematical adapters.
* `QuantitativePlanks/Extensions/`: the arguments removing compactness and finite-volume assumptions.
* `QuantitativePlanks.Equality` and `QuantitativePlanks.Companion`: optional classification and further results.

See [the theorem map](docs/THEOREMS.md) for the precise statements.

## Build

Install [Lean via elan](https://lean-lang.org/install/). The toolchain and
dependencies are pinned. From a fresh checkout:

```sh
lake exe cache get
lake build
```

The default build checks only the main library. To check the optional results:

```sh
lake build +QuantitativePlanks.Extensions +QuantitativePlanks.Equality +QuantitativePlanks.Companion
```

For independent statement comparison and kernel replay, see
[Comparator](verification/README.md).

## Dependencies and provenance

The build uses Mathlib and TauCeti's Brunn–Minkowski formalization; see
[dependency attribution](docs/DEPENDENCIES.md).
No downloaded dependencies or compiled files are included.

Licensed under Apache-2.0; see [LICENSE](LICENSE).
Copyright 2026 Zaz Brown and the contributors named in individual source files.
Existing third-party notices remain applicable.

Zaz Brown directed the research. Proof development and preparation were assisted
by GPT-6 Astra and Claude Fable 5.1.
