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

## Proof Guide

For an outline of the proof and a guide to how the Lean formalization corresponds
to the natural-language proof, see the
[Poincaré proof notes](https://poincare-proof-notes.superliziang.chatgpt.site).

## Installation

From the repository root, with Lean installed:

```sh
lake exe cache get
lake build
```

For [lean-eval benchmark validation](PROBLEM.md), `lake test` additionally requires
comparator, lean4export, landrun, and Nanoda.

## AI Disclaimer

Generative AI (Codex) was used in the development of this codebase. The high-level
architecture is human-designed; AI agents assisted with formalizing individual
proofs and writing boilerplate. All definitions and core theorem statements were
human-verified for correctness. Since all proofs are verified by Lean's type
checker, AI-generated and human-written code are held to the same standard of
correctness.
