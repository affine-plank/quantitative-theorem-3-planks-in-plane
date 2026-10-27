These files extend the compact proof to arbitrary convex sets. `BoundedConvex`
and `FiniteVolume` remove compactness; `Width`, `Quantitative` and `Cover` allow
infinite widths and volume. `Interface` supplies the normalized plank interface
used by the main theorem file.

Import `QuantitativePlanks.Extensions` for the general affine-window versions,
including zero-width planks and reversed endpoints. The compact argument in
`QuantitativePlanks.Proof` does not import these extension files.
