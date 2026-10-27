# Definitions and theorem map

Start with [QuantitativePlanks.lean](../QuantitativePlanks.lean). It defines a
plank as a nonconstant affine function, coerces it to the set where the function
lies between 0 and 1, and defines relative width once. `Point d` means dimension `d`.

## Main theorems

Import `QuantitativePlanks`.

| Result         | Lean declaration                         | Scope                                                         |
| -------------- | ---------------------------------------- | ------------------------------------------------------------- |
| Planar APC     | `QuantitativePlanks.planar_cover`        | Three planks covering any convex planar set                   |
| Planar QAPC    | `QuantitativePlanks.planar_quantitative` | The squared uncovered-area bound for any convex planar set    |
| Two-plank QAPC | `QuantitativePlanks.two_planks`          | The dimension-power bound for any convex set in any dimension |

Only convexity is required of the set: it need not be compact, bounded, closed,
nonempty or of finite volume. Relative widths and volumes take values in `ℝ≥0∞`;
subtraction is truncated at zero. A body with infinite width in a plank's
direction contributes zero relative width. A zero directional span gives
infinite relative width for a positive-width plank.

The public `Plank` represents positive-width planks, as in the earlier qualitative
library. The general affine-window theorems also allow zero-width planks and
reversed endpoints. Their statements remain in
[Extensions](../QuantitativePlanks/Extensions/README.md).

## Proof organization

[QuantitativePlanks/Proof.lean](../QuantitativePlanks/Proof.lean) contains the
compact argument: planar APC, a positive-gap minimum, two-plank QAPC and planar
QAPC. Its geometric lemmas remain in supporting modules.
[Extensions](../QuantitativePlanks/Extensions/) contains the closure and limiting
arguments used by the public noncompact statements. These are separate from
the compact proof. The original `Plank.*` theorem names remain available.

The internal proof convention uses `Point d = Fin (d+1) → ℝ` and `SharpBound d m`
for `m` planks in dimension `d+1`; the public interface uses the actual dimension.

## Optional equality classification

`Quant.PlanarGeometricCatalogue.equality_iff_families` classifies equality in
QAPC for compact positive-area planar bodies and at most three planks with
`0 < R < 1`, and includes the zero-budget case as arbitrary null planks.
`all_budgets_iff` combines this geometric classification for `R < 1` with
the equivalence between equality and covering for `R ≥ 1`.
`all_compact_convex_iff` additionally includes zero-area convex bodies,
where the quantitative equality is automatic.
These are proved theorems, not conjectural family lists. Their exact hypotheses
and family definitions are in
[PlanarGeometricCatalogue](../Plank/Proofs/Quant/PlanarGeometricCatalogue.lean).

## Optional companion results

Import `QuantitativePlanks.Companion` for the tight covering
classification (`Plank.Convex.PlanarTight.AffineClassification.tight_iff`),
the planar `4m`-vertex reduction
(`Plank.PlanarFourMReduction.exists_counterexample_with_at_most_four_mul_vertices`),
simplex sharpness (`Plank.SimplexFacetSharpExample.exact_budget_family`),
constant-width bounds, relative affine transport and other general sufficient
conditions. `Additional/` contains the previously standalone modules needed by
these results; their mathematical module names are preserved.

The generic `SharpBound d m` lemmas are implications, not unconditional proofs
of QAPC for arbitrary `d,m`. The geometric family classification concerns
`0 < R < 1`. At `R ≥ 1`, the wrapper characterizes equality by covering;
it does not provide a geometric catalogue of every covering configuration.
