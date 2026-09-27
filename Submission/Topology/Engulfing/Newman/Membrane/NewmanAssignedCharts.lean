import Submission.Topology.Engulfing.Newman.Data.NewmanGlobalData
import Submission.Topology.Engulfing.Newman.Membrane.NewmanExpansion
import Submission.Topology.Engulfing.Simplicial.Refinement.RefinementRestriction

/-!
# Assigned charts for a finite membrane

A finite stellar refinement fits each source face in one smoothing chart.
Uniformly small perturbations preserve all these chart containments.
-/

namespace PoincareHighDim.Engulfing

open Set Metric Geometry Topology
open scoped ContinuousMap

noncomputable section

set_option linter.unusedSectionVars false

variable {E M : Type*} [DecidableEq E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace M]

/-- One assigned buffered chart contains the whole image of each face. -/
def FacesInAssignedCharts (K : SimplicialComplex ℝ E) {n : ℕ}
    (b : K.faces → BufferedChart M n) (f : C(K.space, M)) : Prop :=
  ∀ s : K.faces, ∀ x : K.space,
    x.1 ∈ convexHull ℝ (s.1 : Set E) → f x ∈ (b s).core

/-- All finitely many assigned-chart conditions have a common perturbation
margin, renewed at each stage of the finite iteration. -/
theorem FacesInAssignedCharts.exists_tolerance (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {n : ℕ} (b : K.faces → BufferedChart M n)
    (f : C(K.space, M)) (hf : FacesInAssignedCharts K b f) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : C(K.space, M), (∀ x, dist (g x) (f x) < δ) →
      FacesInAssignedCharts K b g := by
  classical
  let : Fintype K.faces := hK.fintype
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (hK.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ))
  let A : K.faces → Set K.space := fun s => Subtype.val ⁻¹' convexHull ℝ (s.1 : Set E)
  have hA : ∀ s : K.faces, IsCompact (A s) := fun s =>
    ((s.1.finite_toSet.isCompact_convexHull ℝ).isClosed.preimage continuous_subtype_val).isCompact
  obtain ⟨δ, hδ, hcontrol⟩ := exists_finite_perturbation_control Finset.univ f A
    (fun s => (b s).core) (fun _ => ∅)
    (fun s _ => hA s) (fun s _ => (b s).isOpen_core) (fun _ _ => isClosed_empty)
    (fun s _ y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact hf s x hx)
    (fun _ _ => disjoint_empty _)
  refine ⟨δ, hδ, fun g hg s x hx => ?_⟩
  exact (hcontrol g hg s (Finset.mem_univ _)).1 ⟨x, hx, rfl⟩

/-- Reuse one specific smoothing chart after refining the source and its fixed
subcomplex. Its buffered chart, and hence its assigned core, stay unchanged. -/
def LocalPLChartData.refineSource {K L : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {X : Set M} {n p : ℕ} (b : LocalPLChartData K L f X n p)
    (P J : SimplicialComplex ℝ E) (hspace : P.space = K.space)
    (hJL : SimplicialRefines J L) (hJspace : J.space ⊆ L.space)
    (g : C(P.space, M)) (hg : ∀ x, g x = f ⟨x.1, hspace ▸ x.2⟩) :
    LocalPLChartData P J g X n p where
  toBufferedChart := b.toBufferedChart
  fixed_affine := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hJL s hs
    obtain ⟨A, hA⟩ := b.fixed_affine t ht
    refine ⟨A, fun x hx hxcore => ?_⟩
    rw [hg]
    exact hA ⟨x.1, hspace ▸ x.2⟩ (hst hx) (by rwa [← hg])
  fixed_injective := by
    intro x hx z hz hxz
    have hxz' : b.chart (f ⟨x.1, hspace ▸ x.2⟩) =
        b.chart (f ⟨z.1, hspace ▸ z.2⟩) := by simpa only [← hg] using hxz
    have hxmem : (⟨x.1, hspace ▸ x.2⟩ : K.space) ∈
        Subtype.val ⁻¹' L.space ∩ f ⁻¹' b.toBufferedChart.core := by
      refine ⟨hJspace hx.1, ?_⟩
      change f ⟨x.1, hspace ▸ x.2⟩ ∈ b.toBufferedChart.core
      rw [← hg]
      exact hx.2
    have hzmem : (⟨z.1, hspace ▸ z.2⟩ : K.space) ∈
        Subtype.val ⁻¹' L.space ∩ f ⁻¹' b.toBufferedChart.core := by
      refine ⟨hJspace hz.1, ?_⟩
      change f ⟨z.1, hspace ▸ z.2⟩ ∈ b.toBufferedChart.core
      rw [← hg]
      exact hz.2
    exact Subtype.ext (congrArg (fun w : K.space => w.1) (b.fixed_injective hxmem hzmem hxz'))
  obstacle := b.obstacle
  obstacle_finite := b.obstacle_finite
  obstacle_dimension := b.obstacle_dimension
  obstacle_contains := b.obstacle_contains

/-- A finite refinement with one actual smoothing chart assigned to every face.
It retains all old finite simplex expansions and the precise fixed realization. -/
theorem exists_refinement_with_assigned_local_charts {n p d : ℕ}
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) (f : C(K.space, M))
    {X : Set M} (hX : IsClosed X) (hlocal : HasLocalPLData K L f X n p) :
    ∃ P J : SimplicialComplex ℝ E,
      P.faces.Finite ∧ SimplicialRefines P K ∧ (∀ s ∈ P.faces, s.card ≤ d + 1) ∧
      J.faces ⊆ P.faces ∧ J.space = L.space ∧ SimplicialRefines J L ∧
      (∀ A C, FiniteSimplexExpansionIn K A C → FiniteSimplexExpansionIn P A C) ∧
      ∃ (hspace : P.space = K.space) (g : C(P.space, M)),
        (∀ x, g x = f ⟨x.1, hspace ▸ x.2⟩) ∧
        ∃ b : P.faces → LocalPLChartData P J g X n p,
          FacesInAssignedCharts P (fun s => (b s).toBufferedChart) g := by
  classical
  obtain ⟨b⟩ := hlocal.toFinite hK hX
  obtain ⟨P, I, hP, hspace, href, hdim, hexp, hcharts⟩ :=
    exists_chart_refinement_preserving_expansions K hK f
      (fun i => (b.data i).toBufferedChart) b.covers hd
  let J := complexRestriction P L
  have hJP : J.faces ⊆ P.faces := complexRestriction_faces_subset P L
  have hJS : J.space = L.space := complexRestriction_space_of_refines P K L href hspace hLK
  have hJL : SimplicialRefines J L := complexRestriction_refines_right P L
  let g : C(P.space, M) := f.comp
    ⟨fun x => ⟨x.1, hspace ▸ x.2⟩, continuous_subtype_val.subtype_mk _⟩
  have hg : ∀ x, g x = f ⟨x.1, hspace ▸ x.2⟩ := fun _ => rfl
  choose i hi using (fun s : P.faces => hcharts s.1 s.2)
  let c : P.faces → LocalPLChartData P J g X n p := fun s =>
    (b.data (i s)).refineSource P J hspace hJL hJS.subset g hg
  refine ⟨P, J, hP, href, hdim, hJP, hJS, hJL, hexp, hspace, g, hg, c, ?_⟩
  intro s x hx
  exact (hi s).2 ⟨x.1, hspace ▸ x.2⟩ hx

/-- The invariant preserved between the local moves: the old fixed map and all
assigned chart containments. -/
def AssignedMapCondition (K L : SimplicialComplex ℝ E) (f : C(K.space, M))
    {n : ℕ} (b : K.faces → BufferedChart M n) (g : C(K.space, M)) : Prop :=
  (∀ x : K.space, x.1 ∈ L.space → g x = f x) ∧ FacesInAssignedCharts K b g

/-- A local theorem may return an arbitrarily small perturbation without itself
tracking all the other assigned charts. The common tolerance does that work. -/
def AssignedChartSimplexStep (K L : SimplicialComplex ℝ E) (f : C(K.space, M))
    {n : ℕ} (b : K.faces → BufferedChart M n) (X U : Set M)
    (Base Region : Set E) (p q : ℕ) : Prop :=
  ∀ (C : Set E) (V B : Finset E), IsCompact C → IsSubcomplexSpace K C → Base ⊆ C →
    C ⊆ K.space → C ⊆ (skeleton K p).space → V ∈ K.faces → V.card ≤ q + 2 →
    SimplexAttachment C V B → C ∪ convexHull ℝ (V : Set E) ⊆ Region →
    ∀ (g : C(K.space, M)) (H : M ≃ₜ M), AssignedMapCondition K L f b g →
      X ∪ g '' (Subtype.val ⁻¹' C) ⊆ H '' U →
      ∀ ε : ℝ, 0 < ε → ∃ (g' : C(K.space, M)) (G : M ≃ₜ M),
        (∀ x : K.space, x.1 ∈ L.space → g' x = g x) ∧
        (∀ x, dist (g' x) (g x) < ε) ∧
        X ∪ g' '' (Subtype.val ⁻¹' (C ∪
          (convexHull ℝ (V : Set E) ∩ (skeleton K q).space))) ⊆ G '' (H '' U) ∧
        IsCompact (closure {x | G x ≠ x})

/-- Renew the finite chart tolerance before each move. This converts the actual
local attachment statement to the invariant-preserving iteration interface. -/
theorem AssignedChartSimplexStep.preserves_assigned_charts
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : C(K.space, M))
    {n : ℕ} (b : K.faces → BufferedChart M n) (X U : Set M)
    (Base Region : Set E) (p q : ℕ)
    (hstep : AssignedChartSimplexStep K L f b X U Base Region p q) :
    MapSkeletalSimplexStep K L X U (AssignedMapCondition K L f b) Base Region p q := by
  intro C V B hC hCpoly hBase hCK hCp hV hcard ha hRegion g H hg hcover ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := hg.2.exists_tolerance K hK b g
  obtain ⟨g', G, hfix, hnear, hnew, hcompact⟩ :=
    hstep C V B hC hCpoly hBase hCK hCp hV hcard ha hRegion g H hg hcover
      (min ε δ) (lt_min hε hδ)
  refine ⟨g', G, ⟨?_, ?_⟩, hfix, ?_, hnew, hcompact⟩
  · intro x hx
    exact (hfix x hx).trans (hg.1 x hx)
  · exact hcontrol g' (fun x => (hnear x).trans_le (min_le_right _ _))
  · exact fun x => (hnear x).trans_le (min_le_left _ _)

end

end PoincareHighDim.Engulfing
