# Independent statement checks

On Linux, from the repository root after the normal build, run:

```sh
lake comparator --config verification/comparator.json
```

This uses Comparator built into the pinned Lean 4.35 toolchain. Install
`bubblewrap` (`bwrap`) first; no separate Comparator package is needed.
[Upstream Comparator](https://github.com/leanprover/comparator) now directs users
to this interface. Keep its sandbox enabled.

[`Challenge.lean`](Challenge.lean) independently defines
the geometry and states planar APC, planar QAPC and two-plank QAPC in every
positive dimension, importing only Mathlib. Its three deliberate `sorry`
placeholders are not imported by any proved target. Comparator checks
[`QuantitativePlanks.lean`](../QuantitativePlanks.lean) directly. The comparison
checks theorem types and the definitions they use, permits only `propext`,
`Quot.sound` and `Classical.choice`, and replays the exported solution in Lean's
kernel. There are no definition holes. These are the public noncompact results.
Optional equality classifications and companion results are checked by their
ordinary Lean builds; they are not among these three Comparator statements.

This uses Lean's kernel; no additional independent kernel is enabled. Hosted
GitHub CI has not yet run for this release candidate.
