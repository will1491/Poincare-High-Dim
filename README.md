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
(the "clone of a single generated workspace" submission form; `PROBLEM.md` is the benchmark's
own description of the problem).  The trusted files `Challenge.lean`, `Solution.lean`,
`config.json`, `holes.json`, `lakefile.toml`, `lean-toolchain` and `WorkspaceTest.lean` are
fixed by the benchmark and must not be edited.  Only `Submission.lean` and the modules under
`Submission/` are evaluated; the workspace pins Lean `v4.34.0` and Mathlib `v4.34.0` and admits
no external Lake dependencies, so the whole development lives there:

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

| Module (under `Submission/`) | Content | Reference |
|---|---|---|
| `Morse/Defs.lean` | critical points, Hessian, Morse index, `MorseStrip`, `ModifiedWithin`, `IsSelfIndexing`, `IsHomotopyEquivInclusion` | Milnor §2 |
| `Morse/Existence.lean`, `Morse/ExistenceProof.lean` | existence of Morse functions on a strip (proved: Sard plus `C²`-stability) | Milnor Thm 2.5 |
| `Morse/RegularInterval.lean` | no critical points ⇒ product (proved from the vendored flow theory) | Milnor Thm 3.4 |
| `Morse/SelfIndexing.lean` | self-indexing Morse functions | Milnor Thm 4.8 |
| `Morse/LowHandles.lean` | elimination of index `0, n` and of index `1, n-1` | Milnor Thm 8.1 |
| `Morse/MiddleHandles.lean` | middle-dimensional cancellation (handle complex, Whitney trick) | Milnor Thm 7.8 |
| `HCobordism.lean` | the h-cobordism theorem, assembled from the above | Milnor Thm 9.1 |
| `ModelTransport.lean` | passing from Mathlib's model `𝓡 n` to the model `Fin n → ℝ` | — |
| `Topology/Disk.lean`, `Topology/AlexanderTrick.lean`, `Topology/TwistedSphere.lean` | the Alexander trick; two disks glued along their boundary form a sphere | Milnor Prop. B, Scorpan p. 31 |
| `Topology/SphereSimplyConnected.lean` | `Sᵏ` is simply connected for `k ≥ 2` (not in Mathlib) | Hatcher Prop. 1.14 |
| `ChartDisks.lean` | two disjoint chart disks and the smooth function cutting them out | Scorpan p. 30 |
| `HomotopySphere.lean` | point-set transport along homotopy equivalences; the strip between the disks is an h-cobordism (external) | Hatcher §3.3 |
| `External.lean` | compactness of homotopy spheres; smoothability (Kirby–Siebenmann); the case `n = 5` (Kervaire–Milnor) | — |
| `Smooth.lean` | Smale's theorem for smooth homotopy spheres, `n ≥ 6` and `n ≥ 5` | Milnor Prop. B |

Every remaining `sorry` is a named theorem with a docstring citing the mathematical source;
there are eight of them (`grep -rn sorry Submission`): the four Morse-theoretic nodes
(`exists_selfIndexing`, `exists_no_extremal_index`, `exists_index_in_middle`,
`product_of_middle_indices`), the algebraic-topological input `hcobordism_input_of_homotopy_sphere`,
and the three external theorems in `External.lean`.  Everything else, including the existence of
Morse functions, the regular interval theorem, the assembly of the h-cobordism theorem from its
nodes, the Alexander trick, the twisted-sphere theorem, the chart-disk construction,
`π₁(Sᵏ) = 0`, and the derivation of the target from the smooth theorem, is proved.

## Build and check

```sh
lake exe cache get
lake build
lake test          # runs comparator; needs landrun, lean4export, comparator, nanoda on PATH
```

A submission is accepted only when comparator and the nanoda kernel verify the proof with the
permitted axioms `propext`, `Quot.sound`, `Classical.choice` only, i.e. once every `sorry` is
closed; `#print axioms Submission.poincare_high_dim_topological` shows the current state.
