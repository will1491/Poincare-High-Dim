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
| `Morse/SelfIndexing.lean` with `Morse/{CriticalFinite, MonotoneShift, DistinctValues, ModelField, GradientLike, StripFlow, TrajectoryCutoff, Rearrange, Transversality, Swap}.lean` | self-indexing Morse functions (proved: gradient-like fields with model form in Morse charts, their global flows, distinct critical values, the rearrangement function of Milnor 4.1, general position of the spheres by a level-tangent twist and a Hausdorff-dimension Sard argument, and a bubble sort on inversions) | Milnor Thms 2.8, 3.2, 4.1, 4.4, 4.8 |
| `Morse/LowHandles.lean` with `Morse/{NegDual, DistinctSelfIndexing, Terminal, StripConnected, EqualIndexPosition, Bridge, Isolate, Substrip, CancelPair, IndexOne}.lean` and `Morse/Partner{Defs, Sard, Move, Engines, Circle, Pi1, Birth, Isolate}.lean` | elimination of index `0, n` (Milnor's connectivity argument in flow form, isolation of the cancelling pair, First Cancellation Theorem for an index-`0`/index-`1` pair) and of index `1, n - 1` (each index-`1` point is traded for an index-`3` point: a circle meeting its right sphere once, simple connectivity of the level between indices `2` and `3`, birth of an auxiliary index-`2`/`3` pair in a flow box, isotopy of the circles through general position of maps into the level, realisation by the field, isolation and First Cancellation) — all proved | Milnor Thms 5.4, 8.1, Lemmas 8.2–8.4, 4.2, 4.7, 5.8 |
| `Morse/{CancelSetup, CancelModel, CancelTransverse, CancelField, CancelFlow, CancelFlowTools, CancelGood, CancelFlowP, CancelFlowQ, CancelFlowQ2, CancelFlowExit, CancelGoodExists, CancelFlowBack, CancelFunction, CancelIndexZero}.lean` | the First Cancellation Theorem for an index-`0`/index-`1` pair (proved, ~15,000 lines): the connecting arc and its transverse coordinate, a nowhere-zero alteration `V'` of the gradient-like field along the arc (pushers at `p` and `q`, reversal with a transverse contraction on a one-sided tube), the crossing property of its flow (every trajectory reaches the bottom level forward and the top level backward, by a transported-angle Lyapunov function and the LaSalle principle), and the new Morse function without critical points built from the crossing times | Milnor Thm 5.4, Lemmas 5.5–5.6 |
| `Morse/{CancellingPair, CrossFieldDefs, FirstCancellation, CrossingField, CrossingFlow, CrossFieldDynamics, CrossFieldArc, CrossFieldLift, CrossFieldBand, TransverseAscent}.lean` | the First Cancellation Theorem for adjacent indices `λ, λ + 1` (`IsCancellingPair`: the two spheres meet once, transversally): a Lyapunov function near the connecting arc, built from the Morse charts of both points and a virtual chart of `q` continued along the flow, yields a modified field all of whose trajectories cross the strip (no return by the uniqueness of the connecting trajectory), and the crossing times give a function without critical points — all proved | Milnor Thm 5.4 |
| `Morse/MiddleHandles.lean` with `Morse/MiddleStep.lean` and `Morse/Middle{Sard, Transport, Block, Homology, HandleHomology, Levels, Whitney, Slide, Assembly}.lean` | middle-dimensional cancellation: block configuration at the minimal index, signed Sard counts, the handle homology of a slab computing `H_*(W, V₀)` and forcing a row of gcd `1`, Euclid's algorithm by handle slides, the Whitney trick (Whitney disc, framing, isotopy in a level) removing pairs of opposite intersection points, isolation and the First Cancellation Theorem — all proved | Milnor Thms 6.6, 7.2–7.8 |
| `HCobordism.lean` | the h-cobordism theorem (strip form, dimension `≥ 6`), assembled from the above — proved | Milnor Thm 9.1 |
| `ModelTransport.lean` | passing from Mathlib's model `𝓡 n` to the model `Fin n → ℝ` | — |
| `Topology/Disk.lean`, `Topology/AlexanderTrick.lean`, `Topology/TwistedSphere.lean` | the Alexander trick; two disks glued along their boundary form a sphere | Milnor Prop. B, Scorpan p. 31 |
| `Topology/SphereSimplyConnected.lean` | `Sᵏ` is simply connected for `k ≥ 2` (not in Mathlib) | Hatcher Prop. 1.14 |
| `ChartDisks.lean` | two disjoint chart disks and the smooth function cutting them out | Scorpan p. 30 |
| `HomotopySphere.lean`, `Topology/GeneralPosition.lean`, `Topology/PushOff.lean` | the h-cobordism input (all proved): the complement `W` of two chart disks in a homotopy `n`-sphere (`n ≥ 3`) is simply connected (general position via Hausdorff dimension) and `H_*(W, ∂₀W; ℤ) = 0` | Hatcher 1.14, §3.3 |
| `External.lean` | compactness, smoothability of topological homotopy spheres, and the smooth case `n = 5` — all proved | Hatcher 3.29; Newman; Connell |
| `Smooth.lean`, `SmoothFive.lean` | smooth Poincaré for `n ≥ 5`, using the direct h-cobordism argument for `n ≥ 6` and the rounded-product argument for dimension five | Milnor Prop. B; Brown's Schoenflies theorem |
| `AcyclicFilling.lean`, `RoundedFilling.lean`, `Morse/RoundedCollar.lean` | recognize a simply connected acyclic filling with simply connected boundary as a disk in dimension `≥ 6`; apply this to the rounded product of a punctured homotopy sphere | Smale's h-cobordism theorem |
| `Topology/BrownSchoenflies.lean` and `Topology/Cellular*.lean` | cellular shrinking, one- and two-fiber recognition, and boundary-preserving disk parametrizations for the two sides of a specified spherical collar | Brown, *A Proof of the Generalized Schoenflies Theorem* (1960) |
| `Topology/Engulfing/NewmanTheorem.lean` and its supporting modules | relative topological engulfing by dimension induction, joint source/obstacle general position, and finite skeletal membrane iteration | Newman, *The Engulfing Theorem for Topological Manifolds* |
| `Topology/Engulfing/ConnellFromNewman.lean`, `Topology/TwoOpenCells.lean`, `Topology/PoincareFromNewman.lean` | engulfing produces a two-cell cover; sphere recognition gives a homeomorphism, which transports the standard smooth atlas | Connell; Brown |
| `Homology/*.lean` | singular homology of pairs: long exact sequence, naturality, reduced `H₀`, barycentric subdivision and small simplices (Hatcher 2.21), Mayer–Vietoris (absolute and relative), excision, `H_k(Sⁿ)`, compact supports, local homology of manifolds (Hatcher 3.27(a)), injectivity and surjectivity of `H_n(M) → H_n(M, M∖x)` for closed connected manifolds via ℤ/d coefficients and a Bockstein sequence, `H_n = 0` for noncompact manifolds (Hatcher 3.29) — all proved | Hatcher §2.1–2.2, §3.3 |

Both former proof gaps in `External.lean` are closed. There are no remaining proof
placeholders or added axioms. Smoothability follows from relative topological engulfing,
Connell's two-cell cover, Brown's sphere recognition, and transport of the standard smooth atlas.
The smooth case `n = 5` is proved by puncturing the sphere, rounding the product of its
complement with the real line, applying six-dimensional h-cobordism, and recognizing the
collared halves of the resulting sphere as disks by Brown's theorem.

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

```sh
lake exe cache get
lake build
lake test          # runs comparator; needs landrun, lean4export, comparator, nanoda on PATH
```

A submission is accepted only when comparator and the nanoda kernel verify the proof with the
permitted axioms `propext`, `Quot.sound`, `Classical.choice` only;
`#print axioms Submission.poincare_high_dim_topological` shows its dependencies.
