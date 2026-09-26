import Submission.Topology.Engulfing.NewmanAssignedCharts

/-!
# A core-protected version of the Newman problem

This interface keeps a closed set pointwise fixed instead of treating it as a
polyhedral obstacle. Connectivity and smoothing charts are required only off
that set. The original source map may still meet the core on already covered
or inert parts of its domain.
-/

namespace PoincareHighDim.Engulfing

open Set Metric Geometry Topology
open scoped ContinuousMap

noncomputable section

set_option linter.unusedSectionVars false

variable {M : Type*} [MetricSpace M]

/-- A map change preserves the core fibers, including their exact values. -/
def PreservesCoreValues {Z : Type*} (C : Set M) (f g : Z → M) : Prop :=
  (∀ x, g x ∈ C ↔ f x ∈ C) ∧ ∀ x, f x ∈ C → g x = f x

theorem PreservesCoreValues.refl {Z : Type*} (C : Set M) (f : Z → M) :
    PreservesCoreValues C f f := ⟨fun _ => Iff.rfl, fun _ _ => rfl⟩

theorem PreservesCoreValues.trans {Z : Type*} {C : Set M} {f g h : Z → M}
    (hfg : PreservesCoreValues C f g) (hgh : PreservesCoreValues C g h) :
    PreservesCoreValues C f h :=
  ⟨fun x => (hgh.1 x).trans (hfg.1 x),
    fun x hx => (hgh.2 x ((hfg.1 x).mpr hx)).trans (hfg.2 x hx)⟩

/-- A homeomorphism fixing the core restricts to its complement. -/
def homeomorphCoreComplement (C : Set M) (e : M ≃ₜ M)
    (he : ∀ x ∈ C, e x = x) : ↥(Cᶜ) ≃ₜ ↥(Cᶜ) :=
  e.subtype (by
    intro x
    change x ∉ C ↔ e x ∉ C
    constructor
    · intro hx hex
      have heq : e x = x := e.injective (he (e x) hex)
      exact hx (heq ▸ hex)
    · intro hx hxc
      exact hx ((he x hxc).symm ▸ hxc))

/-- Both sphere-extension ranges are imposed in the complement of the core. -/
def CoreProtectedConnectivity (C U : Set M) (p : ℕ) : Prop :=
  NewmanConnectivity ↥(Cᶜ) (Subtype.val ⁻¹' U) p

theorem CoreProtectedConnectivity.mono {C U : Set M} {p r : ℕ}
    (h : CoreProtectedConnectivity C U p) (hrp : r ≤ p) :
    CoreProtectedConnectivity C U r := NewmanConnectivity.mono h hrp

theorem CoreProtectedConnectivity.image {C U : Set M} {p : ℕ}
    (h : CoreProtectedConnectivity C U p) (e : M ≃ₜ M)
    (he : ∀ x ∈ C, e x = x) : CoreProtectedConnectivity C (e '' U) p := by
  let c := homeomorphCoreComplement C e he
  have hsets : c '' (Subtype.val ⁻¹' U) =
      (Subtype.val ⁻¹' (e '' U) : Set ↥(Cᶜ)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      have hxc : x ∈ Cᶜ := by
        intro hxc
        have hex : e x ∈ C := (he x hxc).symm ▸ hxc
        exact y.2 (hxy ▸ hex)
      exact ⟨⟨x, hxc⟩, hx, Subtype.ext hxy⟩
  change NewmanConnectivity ↥(Cᶜ) (Subtype.val ⁻¹' (e '' U)) p
  rw [← hsets]
  exact NewmanConnectivity.image h c

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smoothing charts are needed only away from the core, and their full source
avoids it, so chart-supported ambient moves fix the core automatically. -/
def HasLocalPLDataOffCore (K L : SimplicialComplex ℝ E) (f : C(K.space, M))
    (C : Set M) (n p : ℕ) : Prop :=
  ∀ y ∉ C, ∃ b : LocalPLChartData K L f ∅ n p,
    y ∈ b.toBufferedChart.core ∧ Disjoint b.chart.source C

theorem HasLocalPLDataOffCore.withMap {K L : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {C : Set M} {n p : ℕ}
    (h : HasLocalPLDataOffCore K L f C n p) (g : C(K.space, M))
    (hfix : ∀ x : K.space, x.1 ∈ L.space → g x = f x) :
    HasLocalPLDataOffCore K L g C n p := by
  intro y hy
  obtain ⟨b, hb, hsource⟩ := h y hy
  exact ⟨b.withMap g hfix, hb, hsource⟩

/-- Data for the alternative induction. The closed core has no polyhedral or
dimension hypothesis; it is protected by the support of the ambient moves. -/
structure CoreProtectedNewmanProblem (E M : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MetricSpace M] (n p q : ℕ) where
  source : SimplicialComplex ℝ E
  fixed : SimplicialComplex ℝ E
  target : SimplicialComplex ℝ E
  source_finite : source.faces.Finite
  fixed_subcomplex : fixed.faces ⊆ source.faces
  target_subcomplex : target.faces ⊆ source.faces
  source_dimension : ∀ s ∈ source.faces, s.card ≤ p + 2
  target_dimension : ∀ s ∈ target.faces, s.card ≤ p + 1
  map : C(source.space, M)
  fixed_injective : InjOn map (Subtype.val ⁻¹' fixed.space)
  core : Set M
  openSet : Set M
  core_closed : IsClosed core
  open_openSet : IsOpen openSet
  core_subset : core ⊆ openSet
  localData : HasLocalPLDataOffCore source fixed map core n p
  codimension : p + 3 ≤ n
  connectivity : CoreProtectedConnectivity core openSet p
  decomposition : EngulfingDecomposition source target map openSet q

def CoreProtectedNewmanProblem.Conclusion {n p q : ℕ}
    (P : CoreProtectedNewmanProblem E M n p q) (ε : ℝ) : Prop :=
  ∃ (g : C(P.source.space, M)) (h : M ≃ₜ M),
    (∀ x : P.source.space, x.1 ∈ P.fixed.space → g x = P.map x) ∧
    PreservesCoreValues P.core P.map g ∧
    (∀ x, dist (g x) (P.map x) < ε) ∧
    P.core ∪ g '' (Subtype.val ⁻¹' P.target.space) ⊆ h '' P.openSet ∧
    (∀ x ∈ P.core, h x = x) ∧ IsCompact (closure {x | h x ≠ x})

theorem CoreProtectedNewmanProblem.conclusion_zero {n p : ℕ}
    (P : CoreProtectedNewmanProblem E M n p 0) {ε : ℝ} (hε : 0 < ε) :
    P.Conclusion ε := by
  refine ⟨P.map, Homeomorph.refl M, fun _ _ => rfl,
    PreservesCoreValues.refl _ _, fun _ => by simpa using hε, ?_, fun _ _ => rfl, ?_⟩
  · intro y hy
    refine ⟨y, ?_, rfl⟩
    exact hy.elim (fun hy => P.core_subset hy)
      (fun hy => P.decomposition.to_outsideDimension.zero_covered hy)
  · simp

/-- The conclusion still supplies the usual target coverage, with the core as
a protected set, but also records the pointwise and source-fiber information. -/
theorem CoreProtectedNewmanProblem.Conclusion.to_newmanConclusion {n p q : ℕ}
    {P : CoreProtectedNewmanProblem E M n p q} {ε : ℝ} (h : P.Conclusion ε) :
    NewmanConclusion P.source P.fixed P.target P.map P.core P.openSet ε := by
  obtain ⟨g, H, hfix, _, hnear, hcover, _, hcompact⟩ := h
  exact ⟨g, H, hfix, hnear, hcover, hcompact⟩

def CoreProtectedRelativeNewmanAt (M : Type*) [MetricSpace M] (n p q : ℕ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    ∀ P : CoreProtectedNewmanProblem E M n p q, ∀ ε : ℝ, 0 < ε → P.Conclusion ε

theorem coreProtectedRelativeNewmanAt_zero (n p : ℕ) :
    CoreProtectedRelativeNewmanAt M n p 0 := by
  intro E _ _ _ P ε hε
  exact P.conclusion_zero hε

/-- A core-disjoint attaching face can be filled in the complement. Other
source faces, including already covered faces, are allowed to meet the core. -/
def CoreProtectedSingleSimplexNewmanAt (M : Type*) [MetricSpace M] (n p q : ℕ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    ∀ P : CoreProtectedNewmanProblem E M n p (q + 1), ∀ s : Finset E,
      s ∈ P.target.faces → s.card = q + 1 →
      (∀ t ∈ P.target.faces, t ≠ s →
        ∀ x : P.source.space, x.1 ∈ convexHull ℝ (t : Set E) → P.map x ∈ P.openSet) →
      Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.core →
      ∀ ε : ℝ, 0 < ε → P.Conclusion ε

end

end PoincareHighDim.Engulfing
