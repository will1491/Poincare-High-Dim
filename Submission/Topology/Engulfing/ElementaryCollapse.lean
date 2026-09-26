import Submission.Topology.Engulfing.SimplexEngulfingChart
import Submission.Topology.Engulfing.EngulfingSequence
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-!
# Finite relative simplex expansions

A relative simplex attachment meets the part already present in a nonempty proper
union of facets. Such a union is exactly a lower roof for a vertex split, and hence
is the interface required by the geometric simplex engulfing theorem.
-/

namespace PoincareHighDim.Engulfing

open Set Topology

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The union of the facets opposite the vertices in `B`. -/
def simplexRoof (V B : Finset E) : Set E :=
  ⋃ i ∈ B, convexHull ℝ ((V.erase i : Finset E) : Set E)

/-- A nonempty proper collection of the facets of a simplex. -/
structure ProperSimplexRoof (V B : Finset E) : Prop where
  subset : B ⊆ V
  nonempty : B.Nonempty
  complement_nonempty : (V \ B).Nonempty

theorem simplexRoof_subset (V B : Finset E) :
    simplexRoof V B ⊆ convexHull ℝ (V : Set E) := by
  intro x hx
  obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
  exact convexHull_mono (Finset.erase_subset i V) hx

/-- One elementary expansion relative to the set already present. -/
structure SimplexAttachment (A : Set E) (V B : Finset E) : Prop where
  independent : AffineIndependent ℝ ((↑) : V → E)
  properRoof : ProperSimplexRoof V B
  intersection : A ∩ convexHull ℝ (V : Set E) = simplexRoof V B

namespace SimplexAttachment

variable {A : Set E} {V B : Finset E} (h : SimplexAttachment A V B)

include h in
theorem roof_subset : simplexRoof V B ⊆ A := by
  rw [← h.intersection]
  exact inter_subset_left

include h in
theorem inter_subset_roof : A ∩ convexHull ℝ (V : Set E) ⊆ simplexRoof V B :=
  h.intersection.subset

end SimplexAttachment

/-- A finite sequence of relative simplex expansions. -/
inductive FiniteSimplexExpansion : Set E → Set E → Prop
  | refl (A : Set E) : FiniteSimplexExpansion A A
  | snoc {A C : Set E} {V B : Finset E} : FiniteSimplexExpansion A C →
      SimplexAttachment C V B → FiniteSimplexExpansion A (C ∪ convexHull ℝ (V : Set E))

namespace FiniteSimplexExpansion

variable {A C D : Set E}

theorem subset (h : FiniteSimplexExpansion A C) : A ⊆ C := by
  induction h with
  | refl => exact subset_rfl
  | snoc _ _ ih => exact ih.trans subset_union_left

theorem trans (h₁ : FiniteSimplexExpansion A C) (h₂ : FiniteSimplexExpansion C D) :
    FiniteSimplexExpansion A D := by
  induction h₂ with
  | refl => exact h₁
  | snoc _ ha ih => exact ih.snoc ha

theorem of_attachment {V B : Finset E} (h : SimplexAttachment A V B) :
    FiniteSimplexExpansion A (A ∪ convexHull ℝ (V : Set E)) :=
  (refl A).snoc h

theorem simplex_of_properRoof {V B : Finset E}
    (hv : AffineIndependent ℝ ((↑) : V → E)) (hB : ProperSimplexRoof V B) :
    FiniteSimplexExpansion (simplexRoof V B) (convexHull ℝ (V : Set E)) := by
  have h : SimplexAttachment (simplexRoof V B) V B :=
    ⟨hv, hB, inter_eq_left.mpr (simplexRoof_subset V B)⟩
  simpa only [union_eq_right.mpr (simplexRoof_subset V B)] using of_attachment h

end FiniteSimplexExpansion

/-- A finite relative expansion whose attached simplices are faces of a specified complex. -/
inductive FiniteSimplexExpansionIn (K : Geometry.SimplicialComplex ℝ E) : Set E → Set E → Prop
  | refl (A : Set E) : FiniteSimplexExpansionIn K A A
  | snoc {A C : Set E} {V B : Finset E} : FiniteSimplexExpansionIn K A C →
      V ∈ K.faces → SimplexAttachment C V B →
      FiniteSimplexExpansionIn K A (C ∪ convexHull ℝ (V : Set E))

namespace FiniteSimplexExpansionIn

variable {K : Geometry.SimplicialComplex ℝ E} {A C D : Set E}

theorem forget (h : FiniteSimplexExpansionIn K A C) : FiniteSimplexExpansion A C := by
  induction h with
  | refl => exact .refl _
  | snoc _ _ ha ih => exact ih.snoc ha

theorem subset (h : FiniteSimplexExpansionIn K A C) : A ⊆ C := h.forget.subset

theorem trans (h₁ : FiniteSimplexExpansionIn K A C) (h₂ : FiniteSimplexExpansionIn K C D) :
    FiniteSimplexExpansionIn K A D := by
  induction h₂ with
  | refl => exact h₁
  | snoc _ hv ha ih => exact ih.snoc hv ha

theorem simplex_of_properRoof {V B : Finset E} (hV : V ∈ K.faces)
    (hB : ProperSimplexRoof V B) :
    FiniteSimplexExpansionIn K (simplexRoof V B) (convexHull ℝ (V : Set E)) := by
  have h : SimplexAttachment (simplexRoof V B) V B :=
    ⟨K.indep hV, hB, inter_eq_left.mpr (simplexRoof_subset V B)⟩
  have he := (refl (K := K) (simplexRoof V B)).snoc hV h
  simpa only [union_eq_right.mpr (simplexRoof_subset V B)] using he

end FiniteSimplexExpansionIn

namespace ProperSimplexRoof

variable {V B : Finset E} (h : ProperSimplexRoof V B)

/-- The vertex split whose lower roof is a prescribed proper union of facets. -/
noncomputable def split : SimplexSplit V where
  left := Finset.univ.filter (fun i : V => i.val ∉ B)
  left_nonempty := by
    obtain ⟨i, hi⟩ := h.complement_nonempty
    exact ⟨⟨i, (Finset.mem_sdiff.mp hi).1⟩, by simpa using (Finset.mem_sdiff.mp hi).2⟩
  right_nonempty := by
    obtain ⟨i, hi⟩ := h.nonempty
    exact ⟨⟨i, h.subset hi⟩, by simpa using hi⟩

@[simp] theorem mem_split_right (i : V) : i ∈ h.split.right ↔ i.val ∈ B := by
  simp [split, SimplexSplit.right]

theorem simplexFacet_subtype (i : V) :
    simplexFacet ((↑) : V → E) i = convexHull ℝ ((V.erase i.val : Finset E) : Set E) := by
  unfold simplexFacet
  congr 1
  ext x
  simp only [mem_image, mem_compl_iff, mem_singleton_iff, Finset.mem_coe, Finset.mem_erase,
    Subtype.exists, Subtype.mk.injEq]
  constructor
  · rintro ⟨y, hy, hne, rfl⟩
    exact ⟨fun he => hne (Subtype.ext he), hy⟩
  · rintro ⟨hne, hx⟩
    exact ⟨x, hx, fun he => hne (congrArg Subtype.val he), rfl⟩

theorem split_lowerRoof : h.split.lowerRoof ((↑) : V → E) = simplexRoof V B := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i.val, (h.mem_split_right i).mp hi,
      (simplexFacet_subtype i) ▸ hx⟩
  · intro hx
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
    let i' : V := ⟨i, h.subset hi⟩
    exact mem_iUnion₂.mpr ⟨i', (h.mem_split_right i').mpr hi,
      (simplexFacet_subtype i').symm ▸ hx⟩

end ProperSimplexRoof

end PoincareHighDim.Engulfing
