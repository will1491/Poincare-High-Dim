# The High-Dimensional Poincaré Conjecture in Lean 4

A Lean 4 formalization of the generalized Poincaré conjecture in dimensions
`n ≥ 5`, following Smale’s h-cobordism argument and the topological work of Newman and Connell.

## Highlighted Theorems

Each highlighted theorem is sorry-free and depends only on the three standard Lean
axioms (`propext`, `Classical.choice`, `Quot.sound`).

- **Generalized Poincaré conjecture** —
  [`poincare_high_dim_topological`](../Submission.lean#L33): a Hausdorff topological
  `n`-manifold homotopy equivalent to `Sⁿ` is homeomorphic to `Sⁿ`, for `n ≥ 5`.
- **Smooth h-cobordism theorem (Milnor, Theorem 9.1)** —
  [`milnor_9_1`](../Submission/HCobordismMilnor.lean#L54): a compact, simply connected
  smooth h-cobordism of dimension at least six is diffeomorphic to the cylinder
  `V × [0,1]`, where `V` is one of its two boundary components.

## Foundations

Built on Mathlib, with adapted modules from
[`differential-geometry`](https://github.com/qinz1yang/differential-geometry/tree/4fbccdfc73f986ce59d7bb66e8bb078f8007ffe2).
The upstream [license](../Submission/DifferentialGeometry/LICENSE) and
[attribution](../Submission/DifferentialGeometry/NOTICE) are retained.

## Installation

From the repository root, with Lean installed:

```sh
lake exe cache get
lake build
```

For [lean-eval benchmark validation](PROBLEM.md), `lake test` additionally requires
comparator, lean4export, landrun, and Nanoda.
