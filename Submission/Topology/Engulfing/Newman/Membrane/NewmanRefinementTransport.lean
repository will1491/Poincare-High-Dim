import Submission.Topology.Engulfing.Newman.Membrane.NewmanMembraneIteration

/-!
# Returning a refined attachment map to its original source

An equal-space refinement changes only the triangulation. Transporting a map
back therefore preserves its error and fixed values exactly. The old skeleton
is contained in the refined skeleton, so refined skeletal coverage supplies the
target required by the original attachment step.
-/

namespace PoincareHighDim.Engulfing

open Set Metric Geometry Topology
open scoped ContinuousMap

noncomputable section

set_option linter.unusedSectionVars false

variable {E M : Type*} [DecidableEq E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace M]

/-- Regard a continuous map on a refined realization as a map on the original
realization, without changing its values at any ambient source point. -/
def transportSourceMap {K P : SimplicialComplex ℝ E} (hspace : P.space = K.space)
    (f : C(P.space, M)) : C(K.space, M) :=
  f.comp ⟨(Homeomorph.setCongr hspace).symm, (Homeomorph.setCongr hspace).symm.continuous⟩

@[simp] theorem transportSourceMap_setCongr {K P : SimplicialComplex ℝ E}
    (hspace : P.space = K.space) (f : C(P.space, M)) (x : P.space) :
    transportSourceMap hspace f (Homeomorph.setCongr hspace x) = f x := by
  simp only [transportSourceMap, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    Homeomorph.symm_apply_apply]

theorem transportSourceMap_image {K P : SimplicialComplex ℝ E}
    (hspace : P.space = K.space) (f : C(P.space, M)) (A : Set E) :
    transportSourceMap hspace f '' (Subtype.val ⁻¹' A) = f '' (Subtype.val ⁻¹' A) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(Homeomorph.setCongr hspace).symm x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Homeomorph.setCongr hspace x, hx, transportSourceMap_setCongr hspace f x⟩

/-- General target-set transport. The source target may become smaller when
returning to the original triangulation. -/
theorem exists_map_on_equal_space_of_target_subset
    (K L P J : SimplicialComplex ℝ E) (hspace : P.space = K.space)
    (hJspace : J.space = L.space) (g : C(K.space, M)) (f : C(P.space, M))
    {ε : ℝ} {A B : Set E} {X Y : Set M} (hAB : A ⊆ B)
    (hfix : ∀ x : P.space, x.val ∈ J.space → f x = g (Homeomorph.setCongr hspace x))
    (hnear : ∀ x : P.space, dist (f x) (g (Homeomorph.setCongr hspace x)) < ε)
    (hcover : X ∪ f '' (Subtype.val ⁻¹' B) ⊆ Y) :
    ∃ g' : C(K.space, M),
      (∀ x : K.space, x.val ∈ L.space → g' x = g x) ∧
      (∀ x, dist (g' x) (g x) < ε) ∧
      X ∪ g' '' (Subtype.val ⁻¹' A) ⊆ Y ∧
      (∀ x : P.space, g' (Homeomorph.setCongr hspace x) = f x) := by
  refine ⟨transportSourceMap hspace f, ?_, ?_, ?_, transportSourceMap_setCongr hspace f⟩
  · intro x hx
    have hxJ : ((Homeomorph.setCongr hspace).symm x).val ∈ J.space := by
      rw [hJspace]
      exact hx
    change f ((Homeomorph.setCongr hspace).symm x) = g x
    simpa only [Homeomorph.apply_symm_apply] using hfix ((Homeomorph.setCongr hspace).symm x) hxJ
  · intro x
    change dist (f ((Homeomorph.setCongr hspace).symm x)) (g x) < ε
    simpa only [Homeomorph.apply_symm_apply] using hnear ((Homeomorph.setCongr hspace).symm x)
  · rw [transportSourceMap_image]
    exact (union_subset_union_right X (image_mono (preimage_mono hAB))).trans hcover

/-- The exact convenience form for the outer assigned-chart simplex step.
Only refined skeletal coverage is needed from the inner general-position
iteration. The supplied ambient homeomorphisms remain unchanged. -/
theorem exists_skeletal_map_on_original_source
    (K L P J : SimplicialComplex ℝ E) (href : SimplicialRefines P K)
    (hspace : P.space = K.space) (hJspace : J.space = L.space)
    (g : C(K.space, M)) (f : C(P.space, M))
    (X U : Set M) (H G : M ≃ₜ M) (C : Set E) (V : Finset E) (q : ℕ) {ε : ℝ}
    (hfix : ∀ x : P.space, x.val ∈ J.space → f x = g (Homeomorph.setCongr hspace x))
    (hnear : ∀ x : P.space, dist (f x) (g (Homeomorph.setCongr hspace x)) < ε)
    (hcover : X ∪ f '' (Subtype.val ⁻¹'
      (C ∪ (convexHull ℝ (V : Set E) ∩ (skeleton P q).space))) ⊆ G '' (H '' U)) :
    ∃ g' : C(K.space, M),
      (∀ x : K.space, x.val ∈ L.space → g' x = g x) ∧
      (∀ x, dist (g' x) (g x) < ε) ∧
      X ∪ g' '' (Subtype.val ⁻¹'
        (C ∪ (convexHull ℝ (V : Set E) ∩ (skeleton K q).space))) ⊆ G '' (H '' U) ∧
      (∀ x : P.space, g' (Homeomorph.setCongr hspace x) = f x) := by
  apply exists_map_on_equal_space_of_target_subset K L P J hspace hJspace g f
    (union_subset_union_right C (inter_subset_inter_right _ (href.old_skeleton_subset hspace q)))
    hfix hnear hcover

end

end PoincareHighDim.Engulfing
