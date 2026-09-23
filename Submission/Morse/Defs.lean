import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Morse-theoretic vocabulary in strip form

We follow the *strip convention*: instead of a cobordism triad `(W; V₀, V₁)` we work with a
smooth function `f : M → ℝ` on a boundaryless manifold `M` and two regular values `a < b`;
the cobordism is the strip `f ⁻¹' (Set.Icc a b)`, its ends are the level sets `f ⁻¹' {a}` and
`f ⁻¹' {b}`, and "`W` is a product cobordism" means that some diffeomorphism of `M` carries the
sublevel set `f ⁻¹' (Set.Iic a)` onto `f ⁻¹' (Set.Iic b)`.  This is exactly the convention of
the sorry-free Morse theory in the `DifferentialGeometry` dependency
(`DifferentialGeometry.Topology.Morse`), whose definitions `IsCriticalPointAt`,
`chartHessianAt` and `IsNondegenerateCriticalPointAt` we mirror here at arbitrary universe
levels (the dependency fixes `Type`).

* `IsCriticalPt I f x` : `mfderiv I 𝓘(ℝ, ℝ) f x = 0`.
* `hessianAt I f p` : the Hessian quadratic form of `f` at `p` computed in the chart
  `extChartAt I p`; at a critical point it is independent of the chart.
* `IsNondegenerateCriticalPt`, `morseIndex` : nondegeneracy and the Morse index (number of
  negative eigenvalues).
* `MorseStrip I f a b` : `f` is a Morse function on the strip between the regular values `a < b`.
* `ModifiedWithin f a b g` : `g` agrees with `f` outside the open strip and maps the open strip
  into `Set.Ioo a b`, so that `f` and `g` have the same sublevel sets at `a` and `b`.
* `IsSelfIndexing I f a b` : critical values are ordered by index (Milnor, *Lectures on the
  h-cobordism theorem*, Definition 4.9 in a slightly weaker form).
* `IsHomotopyEquivInclusion A B` : the inclusion `A ↪ B` is a homotopy equivalence.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff ContinuousMap
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- `x` is a critical point of `f`. Definitionally the same as
`DifferentialGeometry.Topology.Morse.IsCriticalPointAt`. -/
def IsCriticalPt (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : Prop :=
  mfderiv I 𝓘(ℝ, ℝ) f x = 0

/-- The bilinear second derivative of `g : E → ℝ` at `y`. -/
def chartHessianBilinAt (g : E → ℝ) (y : E) : LinearMap.BilinForm ℝ E where
  toFun := fun x => (fderiv ℝ (fderiv ℝ g) y x).toLinearMap
  map_add' := by
    intro x y
    ext z
    simp
  map_smul' := by
    intro a x
    ext z
    simp

/-- The Hessian quadratic form of `g : E → ℝ` at `y`. -/
def chartHessianAt (g : E → ℝ) (y : E) : QuadraticForm ℝ E :=
  (chartHessianBilinAt g y).toQuadraticMap

/-- The Hessian of `f : M → ℝ` at `p`, computed in the preferred chart `extChartAt I p`. -/
def hessianAt (I : ModelWithCorners ℝ E H) (f : M → ℝ) (p : M) : QuadraticForm ℝ E :=
  chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)

/-- `p` is a nondegenerate critical point of `f`: the derivative vanishes and the Hessian in the
preferred chart is a nondegenerate quadratic form. Definitionally the same as
`DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt`. -/
def IsNondegenerateCriticalPt (I : ModelWithCorners ℝ E H) (f : M → ℝ) (p : M) : Prop :=
  IsCriticalPt I f p ∧ (QuadraticMap.associated (R := ℝ) (hessianAt I f p)).SeparatingLeft

/-- The Morse index of `f` at `p`: the number of negative eigenvalues of the Hessian in the
preferred chart. -/
def morseIndex (I : ModelWithCorners ℝ E H) (f : M → ℝ) (p : M) : ℕ :=
  sigNeg (hessianAt I f p)

/-- `f` is a Morse function on the strip between the regular values `a < b`: it is smooth, the
strip is compact, `a` and `b` are regular values, and every critical point inside the open strip
is nondegenerate. -/
structure MorseStrip (I : ModelWithCorners ℝ E H) (f : M → ℝ) (a b : ℝ) : Prop where
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f
  lt : a < b
  compact : IsCompact (f ⁻¹' Icc a b)
  regular : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPt I f x
  nondegenerate : ∀ x, f x ∈ Ioo a b → IsCriticalPt I f x → IsNondegenerateCriticalPt I f x

/-- `g` is a modification of `f` supported in the open strip `f ⁻¹' (Set.Ioo a b)`: it agrees
with `f` off the open strip and maps the open strip into `Set.Ioo a b`. Consequently `f` and `g`
have the same strip, the same level sets at `a` and `b`, and the same sublevel sets at `a` and
`b` (see `ModifiedWithin.preimage_Icc` and friends). -/
structure ModifiedWithin (f : M → ℝ) (a b : ℝ) (g : M → ℝ) : Prop where
  eqOn : EqOn g f (f ⁻¹' Ioo a b)ᶜ
  mapsTo : MapsTo g (f ⁻¹' Ioo a b) (Ioo a b)

/-- A Morse function on a strip is *self-indexing* if critical points of smaller index have
smaller critical values. (Milnor's normalisation `f p = index p` is a further rescaling.) -/
def IsSelfIndexing (I : ModelWithCorners ℝ E H) (f : M → ℝ) (a b : ℝ) : Prop :=
  ∀ p q, f p ∈ Ioo a b → f q ∈ Ioo a b → IsCriticalPt I f p → IsCriticalPt I f q →
    morseIndex I f p < morseIndex I f q → f p < f q

/-- The inclusion of `A` into `B` is a homotopy equivalence. -/
def IsHomotopyEquivInclusion {X : Type*} [TopologicalSpace X] (A B : Set X) : Prop :=
  ∃ e : A ≃ₕ B, ∀ x : A, (e x : X) = x

namespace ModifiedWithin

variable {f g : M → ℝ} {a b : ℝ}

-- The lemmas below are pure set theory and do not use the topology of `M`.
omit [TopologicalSpace M]

theorem refl (f : M → ℝ) (a b : ℝ) : ModifiedWithin f a b f :=
  ⟨fun _ _ => rfl, fun _ hx => hx⟩

theorem preimage_Ioo (h : ModifiedWithin f a b g) : g ⁻¹' Ioo a b = f ⁻¹' Ioo a b := by
  ext x
  by_cases hx : f x ∈ Ioo a b
  · exact ⟨fun _ => hx, fun _ => h.mapsTo hx⟩
  · simp only [mem_preimage, h.eqOn hx]

theorem preimage_Icc (h : ModifiedWithin f a b g) : g ⁻¹' Icc a b = f ⁻¹' Icc a b := by
  ext x
  by_cases hx : f x ∈ Ioo a b
  · have hg := h.mapsTo hx
    exact ⟨fun _ => Ioo_subset_Icc_self hx, fun _ => Ioo_subset_Icc_self hg⟩
  · simp only [mem_preimage, h.eqOn hx]

theorem preimage_singleton_left (h : ModifiedWithin f a b g) : g ⁻¹' {a} = f ⁻¹' {a} := by
  ext x
  by_cases hx : f x ∈ Ioo a b
  · have hg := h.mapsTo hx
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h' => (hg.1.ne' h').elim, fun h' => (hx.1.ne' h').elim⟩
  · simp only [mem_preimage, h.eqOn hx]

theorem preimage_singleton_right (h : ModifiedWithin f a b g) : g ⁻¹' {b} = f ⁻¹' {b} := by
  ext x
  by_cases hx : f x ∈ Ioo a b
  · have hg := h.mapsTo hx
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h' => (hg.2.ne h').elim, fun h' => (hx.2.ne h').elim⟩
  · simp only [mem_preimage, h.eqOn hx]

theorem preimage_Iic_left (h : ModifiedWithin f a b g) : g ⁻¹' Iic a = f ⁻¹' Iic a := by
  ext x
  by_cases hx : f x ∈ Ioo a b
  · have hg := h.mapsTo hx
    simp only [mem_preimage, mem_Iic]
    exact ⟨fun h' => absurd h' (not_le.mpr hg.1), fun h' => absurd h' (not_le.mpr hx.1)⟩
  · simp only [mem_preimage, h.eqOn hx]

theorem preimage_Iic_right (h : ModifiedWithin f a b g) : g ⁻¹' Iic b = f ⁻¹' Iic b := by
  ext x
  by_cases hx : f x ∈ Ioo a b
  · have hg := h.mapsTo hx
    simp only [mem_preimage, mem_Iic]
    exact ⟨fun _ => hx.2.le, fun _ => hg.2.le⟩
  · simp only [mem_preimage, h.eqOn hx]

theorem trans {k : M → ℝ} (h₁ : ModifiedWithin f a b g) (h₂ : ModifiedWithin g a b k) :
    ModifiedWithin f a b k := by
  refine ⟨fun x hx => ?_, fun x hx => h₂.mapsTo (h₁.mapsTo hx)⟩
  have hx' : x ∈ (g ⁻¹' Ioo a b)ᶜ := by
    rw [h₁.preimage_Ioo]
    exact hx
  exact (h₂.eqOn hx').trans (h₁.eqOn hx)

end ModifiedWithin

/-- The inclusion of a set into itself is a homotopy equivalence. -/
theorem isHomotopyEquivInclusion_refl {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsHomotopyEquivInclusion A A :=
  ⟨ContinuousMap.HomotopyEquiv.refl A, fun _ => rfl⟩

theorem IsHomotopyEquivInclusion.subset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : IsHomotopyEquivInclusion A B) : A ⊆ B := by
  obtain ⟨e, he⟩ := h
  intro x hx
  have hmem : ((e ⟨x, hx⟩ : B) : X) ∈ B := (e ⟨x, hx⟩).2
  rwa [he ⟨x, hx⟩] at hmem

end

end PoincareHighDim
