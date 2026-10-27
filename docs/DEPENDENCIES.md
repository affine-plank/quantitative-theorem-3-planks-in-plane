# Pinned dependencies and attribution

* **Lean 4.35.0**: the compiler and kernel are selected by `lean-toolchain`.
* **Mathlib**: `cfc55fc58714a59dc06e6e79edc6d1d95140d3c2`,
  [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4),
  Apache-2.0. Its transitive dependencies are pinned in `lake-manifest.json`.
* **TauCeti**: `06c5261cef788be30609819959c79eb16a7f5d52`,
  [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti),
  Apache-2.0. The main proof imports its Brunn–Minkowski theorem through the
  small adapter `ResearchFormalized.BrunnMinkowski`.

`ResearchFormalized/` separates standard mathematics from original plank
arguments: Brunn–Minkowski, compact convex minima, finite-measure convex sets
and extended diameter. Source headers preserve individual attribution and
license notices. Dependencies are obtained from their pinned public repositories.
