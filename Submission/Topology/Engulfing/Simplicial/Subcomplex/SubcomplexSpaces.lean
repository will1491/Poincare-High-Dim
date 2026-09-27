import Submission.Topology.Engulfing.Newman.Protected.NewmanQuotient
import Submission.Topology.Engulfing.Simplicial.Refinement.RefinementSupport
import Submission.Topology.Engulfing.Local.Charts.LocalOptimalApproximation

/-!
# Sets realized by literal subcomplexes

The protected sets in a finite simplex expansion remain realizations of
subcomplexes under unions, intersections, and attachment of old faces.
-/

namespace PoincareHighDim.Engulfing

open Set Geometry

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsSubcomplexSpace (K : SimplicialComplex ℝ E) (C : Set E) : Prop :=
  ∃ R : SimplicialComplex ℝ E, R.faces ⊆ K.faces ∧ R.space = C

namespace IsSubcomplexSpace

variable {K : SimplicialComplex ℝ E} {C D : Set E}

theorem of_faces_subset {R : SimplicialComplex ℝ E} (h : R.faces ⊆ K.faces) :
    IsSubcomplexSpace K R.space := ⟨R, h, rfl⟩

theorem self (K : SimplicialComplex ℝ E) : IsSubcomplexSpace K K.space :=
  ⟨K, subset_rfl, rfl⟩

theorem empty (K : SimplicialComplex ℝ E) : IsSubcomplexSpace K ∅ :=
  ⟨⊥, empty_subset _, SimplicialComplex.space_bot⟩

theorem subset (h : IsSubcomplexSpace K C) : C ⊆ K.space := by
  obtain ⟨R, hR, rfl⟩ := h
  exact subcomplex_space_subset K R hR

theorem union (hC : IsSubcomplexSpace K C) (hD : IsSubcomplexSpace K D) :
    IsSubcomplexSpace K (C ∪ D) := by
  obtain ⟨R, hR, rfl⟩ := hC
  obtain ⟨S, hS, rfl⟩ := hD
  exact ⟨subcomplexPair K R S hR hS, subcomplexPair_faces_subset K R S hR hS,
    subcomplexPair_space K R S hR hS⟩

theorem inter (hC : IsSubcomplexSpace K C) (hD : IsSubcomplexSpace K D) :
    IsSubcomplexSpace K (C ∩ D) := by
  obtain ⟨R, hR, rfl⟩ := hC
  obtain ⟨S, hS, rfl⟩ := hD
  exact ⟨R ⊓ S, fun _ h => hR h.1, subcomplex_inf_space K R S hR hS⟩

theorem iUnion {ι : Type*} {A : ι → Set E} (h : ∀ i, IsSubcomplexSpace K (A i)) :
    IsSubcomplexSpace K (⋃ i, A i) := by
  choose R hR hspace using h
  refine ⟨subcomplexUnion K R hR, subcomplexUnion_faces_subset K R hR, ?_⟩
  rw [subcomplexUnion_space]
  simp only [hspace]

theorem face {s : Finset E} (hs : s ∈ K.faces) :
    IsSubcomplexSpace K (convexHull ℝ (s : Set E)) := by
  refine ⟨vertexRestriction K (convexHull ℝ (s : Set E)), fun _ h => h.1, ?_⟩
  rw [(SimplicialRefines.refl K).vertexRestriction_space hs]
  exact inter_eq_right.mpr (K.convexHull_subset_space hs)

theorem subface {s t : Finset E} (hs : s ∈ K.faces) (ht : t ⊆ s) :
    IsSubcomplexSpace K (convexHull ℝ (t : Set E)) := by
  by_cases hne : t.Nonempty
  · exact face (K.down_closed hs ht hne)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    simpa only [he, Finset.coe_empty, convexHull_empty] using empty K

theorem skeleton (K : SimplicialComplex ℝ E) (p : ℕ) :
    IsSubcomplexSpace K (PoincareHighDim.Engulfing.skeleton K p).space :=
  of_faces_subset (fun _ hs => hs.1)

/-- Geometric containment in a skeleton gives the same dimension bound on
every face of the literal subcomplex realizing the contained set. -/
theorem exists_of_subset_skeleton (h : IsSubcomplexSpace K C) {p : ℕ}
    (hCp : C ⊆ (PoincareHighDim.Engulfing.skeleton K p).space) :
    ∃ R : SimplicialComplex ℝ E, R.faces ⊆ K.faces ∧ R.space = C ∧
      ∀ s ∈ R.faces, s.card ≤ p + 1 := by
  obtain ⟨R, hR, hspace⟩ := h
  refine ⟨R, hR, hspace, ?_⟩
  intro s hs
  have hc := hCp (hspace.subset
    (R.convexHull_subset_space hs (s.centroid_mem_convexHull (R.nonempty_of_mem_faces hs))))
  obtain ⟨t, ht, hct⟩ := SimplicialComplex.mem_space_iff.mp hc
  exact (Finset.card_le_card (face_subset_of_centroid_mem K (hR hs) ht.1 hct)).trans ht.2

/-- Any geometric refinement preserves a set realized by an old subcomplex. -/
theorem refine {P : SimplicialComplex ℝ E} (h : IsSubcomplexSpace K C)
    (href : SimplicialRefines P K) (hspace : P.space = K.space) : IsSubcomplexSpace P C := by
  obtain ⟨R, hR, rfl⟩ := h
  exact ⟨complexRestriction P R, complexRestriction_faces_subset P R,
    complexRestriction_space_of_refines P K R href hspace hR⟩

theorem isCompact [FiniteDimensional ℝ E] (h : IsSubcomplexSpace K C) (hK : K.faces.Finite) :
    IsCompact C := by
  obtain ⟨R, hR, rfl⟩ := h
  exact isCompact_space_of_finite_faces R (hK.subset hR)

end IsSubcomplexSpace

end PoincareHighDim.Engulfing
