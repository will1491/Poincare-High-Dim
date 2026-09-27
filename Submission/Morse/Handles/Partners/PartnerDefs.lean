import Submission.Morse.Cancellation.FirstCancellation
import Submission.Morse.Rearrangement.SelfIndexing
import Submission.Morse.Cancellation.Setup.Isolate
import Submission.Morse.Strips.Terminal
import Submission.Morse.Rearrangement.EqualIndexPosition
import Submission.Morse.Rearrangement.DistinctSelfIndexing
import Submission.Morse.Cancellation.Setup.Bridge
import Submission.Morse.Strips.Substrip
import Submission.Topology.Connectivity.GeneralPosition

set_option autoImplicit false


/-!
# The proof of `exists_index_one_partner` (Milnor 8.1, index 1): overview and definitions

`exists_model_pair` uses Milnor's geometry (index `l + 1` at the smaller coordinate but the higher
value; value bounds instead of `η`-closeness).

Proof structure (`partner_target`, in `Submission/Morse/Handles/Partners/PartnerIsolate.lean`):
1. `exists_top_index_one` (Milnor 4.2): the other index-`1` points are lowered below `p`.
2. `exists_partner_config` = `exists_partner_of_loop ∘ exists_loop_config`:
   * `exists_loop_config` (Milnor 8.3, done directly on the level `c₂` between the index-`2`
     and index-`3` values): an embedded level loop `γ` meeting the right sphere of `p` once,
     transversally, with free descent (`IsLoopConfig`);
   * `exists_partner_of_loop`: `γ` is null-homotopic in the level (`exists_level_nullhomotopy`,
     `π₁(V_{2+}) = 1` in homotopy-lifting form), an index-`2`/`3` pair is born in a flow box above
     `γ 0` and the left circle of the new point `q` is isotoped onto `γ` by a level-tangent
     correction of the field (`exists_birth_along_loop`: Lemmas 8.2, 8.4, 5.8, 4.7);
     output `IsPartnerConfig`.
3. `exists_isolate_partner` = `exists_isolate_of_fine ∘ exists_fine_partner ∘
   exists_small_partner`: constants, no-common-trajectory radius, Milnor 4.2 raising the old
   index-`2` points above `q` (the field is unchanged along the trajectories of `p` and `q`),
   restriction to a substrip and the Sard-map conversion (`sard_of_meetsRightOnce`).

Everything lives in `M`: circles are `1`-periodic maps `ℝ → M`, families are maps `ℝ → ℝ → M`
(`θ` periodic, `s` the family parameter); level sets are never given a manifold structure.
Encoding of the single transverse meeting: `rightFun` is the first integral `J = ‖v‖ • u` of the
landing point at the level `f p + ε`; by definition
`sardMap p hq ε c ε hp (circ2 t) = rightFun p ε c (leftLoop q ε c t)` (`sardMap_circ`, `rfl`).
-/

open Set Filter Function

namespace PoincareHighDim

open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart)

namespace IndexOnePartner

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-! ## 0. Definitions -/

/-- The standard angle parametrisation of the unit circle of `ℝ²` (period `1`). -/
def circ2 (t : ℝ) : Fin 2 → ℝ :=
  ![Real.cos (2 * Real.pi * t), Real.sin (2 * Real.pi * t)]

/-- A **smooth embedded circle on the level `c`**, parametrised `1`-periodically by `ℝ`:
smooth, immersed, injective modulo `1`, with values on `f ⁻¹' {c}`. -/
def IsLevelLoop (I : ModelWithCorners ℝ (Fin n → ℝ) H) (f : M → ℝ) (c : ℝ) (γ : ℝ → M) :
    Prop :=
  Periodic γ 1 ∧ ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ (∀ θ, mfderiv 𝓘(ℝ, ℝ) I γ θ (1 : ℝ) ≠ 0) ∧
    (∀ θ θ', γ θ = γ θ' → ∃ k : ℤ, θ' = θ + k) ∧ ∀ θ, f (γ θ) = c

/-- The slice `θ ↦ h θ s` of a family of loops is a smooth embedding of the circle
(immersed and injective modulo `1`). -/
def IsEmbeddedSlice (I : ModelWithCorners ℝ (Fin n → ℝ) H) (h : ℝ → ℝ → M) (s : ℝ) : Prop :=
  (∀ θ, mfderiv 𝓘(ℝ, ℝ) I (fun θ' => h θ' s) θ (1 : ℝ) ≠ 0) ∧
    ∀ θ θ', h θ s = h θ' s → ∃ k : ℤ, θ' = θ + k

/-- A **continuous homotopy of loops inside the level `c`** from `γ` to `β`
(`θ` is the periodic loop parameter, `s` the homotopy parameter; `s = 0` gives `γ`, `s = 1`
gives `β`). -/
def IsLevelHomotopy (f : M → ℝ) (c : ℝ) (H : ℝ → ℝ → M) (γ β : ℝ → M) : Prop :=
  Continuous (uncurry H) ∧ (∀ θ s, H (θ + 1) s = H θ s) ∧ (∀ θ s, f (H θ s) = c) ∧
    (∀ θ, H θ 0 = γ θ) ∧ ∀ θ, H θ 1 = β θ

/-- `T` is **thin of dimension `d`**: it is covered by countably many images of `C¹` maps from
open subsets of `ℝ^d` (structured thinness: stable under cones and products with intervals, which
the general-position arguments use). -/
def IsThin (I : ModelWithCorners ℝ (Fin n → ℝ) H) (d : ℕ) (T : Set M) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (U : ι → Set (Fin d → ℝ)) (g : ι → (Fin d → ℝ) → M),
    (∀ i, IsOpen (U i)) ∧ (∀ i, ContMDiffOn 𝓘(ℝ, Fin d → ℝ) I 1 (g i) (U i)) ∧
      T ⊆ ⋃ i, g i '' U i

/-- The slices of the family `h` are **embedded on the parameter region `Q`**: the slice
`θ ↦ h θ s` is immersed at every point `(θ, s)` of `Q`, and two points of `Q` on a common slice
with the same image differ by an integer in `θ`.  (`IsEmbeddedSlice I h s` is the case
`Q = ℝ × {s}`.)  It is the invariant of the cell-by-cell
Whitney general-position argument (`eventually_isEmbeddedOn`, `exists_embedded_cell_step`). -/
def IsEmbeddedOn (I : ModelWithCorners ℝ (Fin n → ℝ) H) (h : ℝ → ℝ → M) (Q : Set (ℝ × ℝ)) :
    Prop :=
  (∀ z ∈ Q, mfderiv 𝓘(ℝ, ℝ) I (fun θ => h θ z.2) z.1 (1 : ℝ) ≠ 0) ∧
    ∀ θ θ' s, (θ, s) ∈ Q → (θ', s) ∈ Q → h θ s = h θ' s → ∃ k : ℤ, θ' = θ + k

/-- The open box `{|y j| < ρ (j ≠ i₀), -ρ < y i₀ < L + ρ}` of a flow box. -/
def boxSet (i₀ : Fin n) (ρ L : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ j, j ≠ i₀ → |y j| < ρ) ∧ -ρ < y i₀ ∧ y i₀ < L + ρ}

/-- The inner box `{|y j| < ρ/2 (j ≠ i₀), L/4 < y i₀ < 3L/4}` (where the new function lives). -/
def innerBox (i₀ : Fin n) (ρ L : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ j, j ≠ i₀ → |y j| < ρ / 2) ∧ L / 4 < y i₀ ∧ y i₀ < 3 * L / 4}

/-- The middle box `{|y j| < 3ρ/4 (j ≠ i₀), L/8 < y i₀ < 7L/8}` (where the new field lives). -/
def midBox (i₀ : Fin n) (ρ L : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ j, j ≠ i₀ → |y j| < 3 * ρ / 4) ∧ L / 8 < y i₀ ∧ y i₀ < 7 * L / 8}

/-- The bottom face `{y i₀ = 0, |y j| < ρ (j ≠ i₀)}` of a flow box (a convex ball of the level). -/
def bottomFace (i₀ : Fin n) (ρ : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ j, j ≠ i₀ → |y j| < ρ) ∧ y i₀ = 0}
/-- The squared distance `∑_{j ≠ i₀} (y j)²` from the `i₀`-axis. -/
def offAxisSq (i₀ : Fin n) (y : Fin n → ℝ) : ℝ :=
  ∑ j, if j = i₀ then 0 else y j ^ 2

/-- The diagonal quadratic form `∑_{j ≠ i₀} w j (y j)²` transverse to the `i₀`-axis. -/
def diagQuad (i₀ : Fin n) (w : Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ j, if j = i₀ then 0 else w j * y j ^ 2

/-- **Milnor's tapered birth function** (proof of Lemma 8.2):
`x + s(x) a(r²) + γ(x) Q(y) b(r²)`, with `x = y i₀`, `r² = offAxisSq i₀ y`, `Q = diagQuad i₀ w`. -/
def taperedModel (i₀ : Fin n) (w : Fin n → ℝ) (s a b γ : ℝ → ℝ) (y : Fin n → ℝ) : ℝ :=
  y i₀ + s (y i₀) * a (offAxisSq i₀ y) + γ (y i₀) * diagQuad i₀ w y * b (offAxisSq i₀ y)

section Strip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

/-- The trajectory of `x` descends **freely** for the time `T`: on `[0, T]` it meets no closed
small ball (so it has unit speed and `f (D.flow s x) = f x - s` inside the strip). -/
def DescendsFreely (D : GradientLikeStrip I f a b crit) (T : ℝ) (x : M) : Prop :=
  ∀ s ∈ Icc 0 T, ∀ p (hp : p ∈ crit), D.flow s x ∉ D.closedSmallBall p hp

/-- The trajectory of `x` ascends freely for the time `T` (backward flow on `[-T, 0]`). -/
def AscendsFreely (D : GradientLikeStrip I f a b crit) (T : ℝ) (x : M) : Prop :=
  ∀ s ∈ Icc (-T) 0, ∀ p (hp : p ∈ crit), D.flow s x ∉ D.closedSmallBall p hp

/-- The chart images of all critical points are `δ`-thin in level. -/
def IsFineAt (D : GradientLikeStrip I f a b crit) (δ : ℝ) : Prop :=
  ∀ x (hx : x ∈ crit),
    (D.chart x hx).χ '' Metric.ball 0 (D.chart x hx).R' ⊆ f ⁻¹' Ioo (f x - δ) (f x + δ)

/-- The point of the model left circle of the index-`2` point `q` (at the level `f q - ε`) in the
direction `circ2 t`. -/
def leftPt (D : GradientLikeStrip I f a b crit) (q : M) (hq : q ∈ crit)
    (hk : (D.chart q hq).k = 2) (ε t : ℝ) : M :=
  (D.chart q hq).χ ((D.chart q hq).sphereParam ε (fun i => circ2 t (Fin.cast hk i)))

/-- The **left loop** of an index-`2` point `q` at the level `c`: the time-`(f q - ε - c)` flow
image of the model left circle, parametrised by the angle. -/
def leftLoop (D : GradientLikeStrip I f a b crit) (q : M) (hq : q ∈ crit)
    (hk : (D.chart q hq).k = 2) (ε c : ℝ) : ℝ → M :=
  fun t => D.flow (f q - ε - c) (leftPt D q hq hk ε t)

/-- The **right function** of `p` at the level `c`: the first integral `J = ‖v‖ • u` of the point
reached at the time `c - (f p + ε)` (the landing point at the level `f p + ε`), read in the chart
of `p`.  On the level `c` its zero set inside `rightDom` is the right sphere of `p`. -/
def rightFun (D : GradientLikeStrip I f a b crit) (p : M) (hp : p ∈ crit) (ε c : ℝ) (x : M) :
    EuclideanSpace ℝ (Fin (D.chart p hp).k) :=
  ModelField.J (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow (c - (f p + ε)) x))

/-- The domain of `rightFun`: the landing point lies in the normal-form ball of `p`
(the `sardDom` condition). -/
def rightDom (D : GradientLikeStrip I f a b crit) (p : M) (hp : p ∈ crit) (ε c : ℝ) : Set M :=
  {x | D.flow (c - (f p + ε)) x ∈ (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R}}

/-- **The loop `γ` meets the right sphere of `p` exactly once, transversally** (in the
`J`-encoding): `rightFun ∘ γ` has, on `rightDom`, exactly one zero modulo `1`, with a nonzero
derivative there. -/
def MeetsRightOnce (D : GradientLikeStrip I f a b crit) (p : M) (hp : p ∈ crit) (ε c : ℝ)
    (γ : ℝ → M) : Prop :=
  ∃ t₀ : ℝ, γ t₀ ∈ rightDom D p hp ε c ∧ rightFun D p hp ε c (γ t₀) = 0 ∧
    (∀ t, γ t ∈ rightDom D p hp ε c → rightFun D p hp ε c (γ t) = 0 → ∃ m : ℤ, t = t₀ + m) ∧
    ∃ v, HasDerivAt (fun t => rightFun D p hp ε c (γ t)) v t₀ ∧ v ≠ 0

/-- **A level-preserving smooth embedded annulus** in the collar `f ⁻¹' [c, c']` from the loop
`γ` (level `c`, `s = 0`) to the loop `β` (level `c'`, `s = 1`), vertical (a piece of trajectory
of `D`) near both ends: the in-`M` form of an isotopy of the level `c`. -/
def IsLevelAnnulus (D : GradientLikeStrip I f a b crit) (c c' : ℝ) (A : ℝ → ℝ → M)
    (γ β : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry A) ∧ (∀ θ s, A (θ + 1) s = A θ s) ∧
    (∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, f (A θ s) = c + s * (c' - c)) ∧
    (∀ θ θ', ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, A θ s = A θ' s' →
      s = s' ∧ ∃ k : ℤ, θ' = θ + k) ∧
    (∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, mfderiv 𝓘(ℝ, ℝ) I (fun θ' => A θ' s) θ (1 : ℝ) ≠ 0) ∧
    ∃ η > 0, (∀ θ, ∀ s ∈ Icc 0 η, A θ s = D.flow (-(s * (c' - c))) (γ θ)) ∧
      ∀ θ, ∀ s ∈ Icc (1 - η) 1, A θ s = D.flow ((1 - s) * (c' - c)) (β θ)

/-- **A flow box** of the gradient-like strip `D` over the point `x₀` (on the level `c`), of
height `L` and width `ρ`: a smooth chart `ψ` on `boxSet i₀ ρ L` in which `f = c + y i₀` and the
flow of `D` is the translation `y ↦ y - s • e_{i₀}`, avoiding all Morse chart images. -/
structure FlowBox (D : GradientLikeStrip I f a b crit) (x₀ : M) (c L ρ : ℝ) where
  /-- the chart -/
  ψ : OpenPartialHomeomorph (Fin n → ℝ) M
  /-- the vertical coordinate -/
  i₀ : Fin n
  map_zero : ψ 0 = x₀
  box_subset : boxSet i₀ ρ L ⊆ ψ.source
  smooth : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ ψ ψ.source
  smooth_symm : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm ψ.target
  level : ∀ y ∈ boxSet i₀ ρ L, f (ψ y) = c + y i₀
  vertical : ∀ y ∈ boxSet i₀ ρ L, ∀ s : ℝ, y - s • Pi.single i₀ (1 : ℝ) ∈ boxSet i₀ ρ L →
    D.flow s (ψ y) = ψ (y - s • Pi.single i₀ (1 : ℝ))
  avoid : ∀ y ∈ boxSet i₀ ρ L, ∀ p (hp : p ∈ crit),
    ψ y ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R'

end Strip

end

end IndexOnePartner

end PoincareHighDim
