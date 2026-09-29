# PoincareHighDim

A Lean 4 / Mathlib formalization project for the generalized Poincaré conjecture in
dimensions `n ≥ 5`, following Smale's Morse-theoretic (h-cobordism) route, laid out as a
submission workspace for the [lean-eval](https://github.com/leanprover/lean-eval) problem
`poincare_high_dim_topological`.

The target theorem is the `proof_wanted` statement
`ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere` of
`Mathlib.Geometry.Manifold.PoincareConjecture`, restricted to `5 ≤ n`:

```lean
theorem poincare_high_dim_topological {n : ℕ} (_h5 : 5 ≤ n)
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (_h : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
```

## Layout

This repository *is* the lean-eval benchmark workspace for `poincare_high_dim_topological`
(the "clone of a single generated workspace" submission form; [PROBLEM.md](PROBLEM.md) is the
benchmark's own description of the problem).  The trusted files `Challenge.lean`, `Solution.lean`,
`config.json`, `holes.json`, `lakefile.toml`, `lean-toolchain` and `WorkspaceTest.lean` are
fixed by the benchmark and must not be edited.  Only `Submission.lean` and the modules under
`Submission/` are evaluated; the workspace pins Lean `v4.34.0` and Mathlib `v4.34.0` and admits
no external Lake dependencies, so the whole development lives there. All paths below are
relative to the repository root:

* `Submission.lean` proves `Submission.poincare_high_dim_topological` (the hole named in
  `holes.json`; `Solution.lean` bridges it to the trusted statement).
* `Submission/` is the development (namespace `PoincareHighDim`), in Milnor's *strip form*:
  a smooth `f : M → ℝ` with regular values `a < b` plays the role of a cobordism
  `f ⁻¹' (Set.Icc a b)`, and "product cobordism" means that a diffeomorphism of `M` carries
  `f ⁻¹' (Set.Iic a)` onto `f ⁻¹' (Set.Iic b)`.
* `Submission/DifferentialGeometry/` is a vendored copy (Apache License 2.0, see the `LICENSE`
  and `NOTICE` there) of the part of
  [qinz1yang/differential-geometry](https://github.com/qinz1yang/differential-geometry)
  (commit `4fbccdfc`) that the regular interval theorem needs: flows of compactly supported
  vector fields with smooth dependence on initial conditions, unit-speed vector fields on a
  strip, and the Morse-theoretic definitions.  Relative to upstream its statements are
  generalised from analytic to smooth atlases and from `Type` to `Type*`, one Mathlib import
  was added, one `set_option` moved from the lakefile into the file, and deprecated names were
  updated for Mathlib `v4.34.0`.

The main directories and proof components are:

| Location | Content | Reference |
|---|---|---|
| `Submission/Morse/` | Morse functions, regular strips, self-indexing, and handle cancellation. | Milnor §§2–8 |
| `Submission/HCobordism.lean` | Smooth h-cobordism in strip form, dimension `≥ 6`. | Milnor Thm 9.1 |
| `Submission/Homology/` | Relative homology, excision, Mayer–Vietoris, and sphere and manifold homology. | Hatcher §§2–3 |
| `Submission/Manifold/`, `Submission/HomotopySphere.lean` | Chart disks, model transport, and the h-cobordism setup for homotopy spheres. | Scorpan pp. 30–31; Hatcher §3.3 |
| `Submission/Topology/Disks/`, `Submission/Topology/Connectivity/` | The Alexander trick, disk gluing, and connectivity of disk complements. | Milnor Prop. B; Hatcher Prop. 1.14 |
| `Submission/Filling/`, `Submission/SmoothFive.lean` | Rounded fillings and the dimension-five smooth Poincaré argument. | Smale; Brown |
| `Submission/Topology/Schoenflies/` | Brown's Schoenflies theorem via cellular shrinking. | Brown (1960) |
| `Submission/Topology/Engulfing/`, `Submission/Topology/Recognition/` | Newman engulfing, Connell's two-cell cover, and sphere recognition. | Newman; Connell; Brown |
| `Submission/Smooth.lean`, `Submission/External.lean` | Smooth Poincaré for `n ≥ 5`, compactness, and smoothability. | Milnor Prop. B; Newman; Connell |
| `docs/` | README and benchmark problem description. | — |

The development uses the standard axioms only (`#print axioms`: `propext`,
`Classical.choice`, `Quot.sound`): in particular the smooth h-cobordism theorem in dimension
`≥ 6` (`hcobordism_strip`) and Smale's theorem for smooth homotopy spheres of dimension `n ≥ 5`
(`poincare_smooth`), with the existence of Morse functions, self-indexing, the regular
interval theorem, the elimination of the indices `0, 1, n - 1, n`, the First Cancellation
Theorem, the middle-dimensional cancellation (handle homology, handle slides, the Whitney trick),
the Alexander trick, the twisted-sphere theorem, the chart-disk construction, `π₁(Sᵏ) = 0`, the
h-cobordism input, the compactness of homotopy spheres, and the derivation of the target from the
smooth theorem. `Submission.poincare_high_dim_topological` has the same three standard
axioms and does not depend on `sorryAx`.

## Build and check

Run these commands from the repository root (the directory containing `lakefile.toml`),
not from `docs/`:

```sh
lake exe cache get
lake build
lake test          # runs comparator; needs landrun, lean4export, comparator, nanoda on PATH
```

A submission is accepted only when comparator and the nanoda kernel verify the proof with the
permitted axioms `propext`, `Quot.sound`, `Classical.choice` only;
`#print axioms Submission.poincare_high_dim_topological` shows its dependencies.
