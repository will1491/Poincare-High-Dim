/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.RegularLevel.SmoothAtlas
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# The smooth interior as a boundaryless ambient manifold

Restricting extended charts to the manifold interior gives an atlas modeled on the whole
model vector space. The inclusion and the smoothness-detection criterion identify this
atlas with the original smooth structure on the interior.
-/

namespace PoincareHighDim

open Set Topology
open scoped Manifold ContDiff

instance euclideanHalfSpace_secondCountable (n : ℕ) [NeZero n] :
    SecondCountableTopology (EuclideanHalfSpace n) :=
  inferInstanceAs (SecondCountableTopology {x : EuclideanSpace ℝ (Fin n) // 0 ≤ x 0})

namespace ManifoldInterior

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace W] [ChartedSpace H W]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ W]

/-- An inverse extended chart carries the interior of its target to the manifold interior. -/
theorem extChartAt_symm_mem_interior (x : W) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) :
    (extChartAt I x).symm y ∈ I.interior W := by
  have ht : y ∈ (extChartAt I x).target := interior_subset hy
  have hs := (extChartAt I x).map_target ht
  rw [extChartAt_source] at hs
  apply (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
    (chart_mem_atlas H x) hs).mpr
  change (extChartAt I x) ((extChartAt I x).symm y) ∈
    interior (extChartAt I x).target
  rwa [(extChartAt I x).right_inv ht]

/-- Interior points admit full Euclidean charts with the original ambient extensions. -/
theorem exists_chart (x : I.interior W) :
    ∃ e : OpenPartialHomeomorph (I.interior W) E,
      x ∈ e.source ∧
      e.source = Subtype.val ⁻¹' (extChartAt I x.1).source ∧
      e.target = interior (extChartAt I x.1).target ∧
      (∀ y, e y = extChartAt I x.1 y.1) ∧
      ∀ y ∈ e.target, (e.symm y).1 = (extChartAt I x.1).symm y := by
  classical
  let ψ := extChartAt I x.1
  let F : I.interior W → E := fun y => ψ y.1
  let G : E → I.interior W := fun y =>
    if hy : ψ.symm y ∈ I.interior W then ⟨ψ.symm y, hy⟩ else x
  have hG (y : E) (hy : y ∈ interior ψ.target) : (G y).1 = ψ.symm y := by
    have hh : ψ.symm y ∈ I.interior W := extChartAt_symm_mem_interior I x.1 hy
    dsimp only [G]
    rw [dite_eq_left hh]
  have hF (y : I.interior W) (hy : y.1 ∈ ψ.source) :
      F y ∈ interior ψ.target := by
    exact (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas H x.1) (by simpa only [ψ, extChartAt_source] using hy)).mp y.2
  let e : OpenPartialHomeomorph (I.interior W) E :=
    { toFun := F
      invFun := G
      source := Subtype.val ⁻¹' ψ.source
      target := interior ψ.target
      map_source' := hF
      map_target' := by
        intro y hy
        change (G y).1 ∈ ψ.source
        rw [hG y hy]
        exact ψ.map_target (interior_subset hy)
      left_inv' := by
        intro y hy
        apply Subtype.ext
        rw [hG (F y) (hF y hy)]
        exact ψ.left_inv hy
      right_inv' := by
        intro y hy
        change ψ (G y).1 = y
        rw [hG y hy]
        exact ψ.right_inv (interior_subset hy)
      open_source := (isOpen_extChartAt_source (I := I) x.1).preimage continuous_subtype_val
      open_target := isOpen_interior
      continuousOn_toFun := (continuousOn_extChartAt x.1).comp
        continuous_subtype_val.continuousOn (fun y hy => hy)
      continuousOn_invFun := by
        apply continuousOn_iff_continuous_domRestrict.mpr
        apply continuous_induced_rng.mpr
        exact continuousOn_iff_continuous_domRestrict.mp
          (((continuousOn_extChartAt_symm x.1).mono interior_subset).congr hG) }
  exact ⟨e, mem_extChartAt_source x.1, rfl, rfl, fun _ => rfl, hG⟩

/-- The induced smooth structure on the interior is modeled on the entire vector space,
so its model with corners is boundaryless. -/
noncomputable def inducedAtlas : InducedAtlas I (I.interior W) E := by
  classical
  choose e hmem hsource htarget hmap hinv using exists_chart I (W := W)
  exact
    { chart := e
      mem_source := hmem
      ambientSource := fun x => (extChartAt I x.1).source
      open_ambientSource := fun x => isOpen_extChartAt_source (I := I) x.1
      source_eq := hsource
      extension := fun x => extChartAt I x.1
      extension_eq := fun x y _ => (hmap x y).symm
      smooth_extension := fun x => by
        simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (x := x.1))
      smooth_inverse := fun x =>
        ((contMDiffOn_extChartAt_symm x.1).mono (htarget x ▸ interior_subset)).congr
          (hinv x) }

/-- The interior of a compact manifold is sigma compact. The original model supplies
second countability, while the Euclidean interior atlas supplies local compactness. -/
theorem sigmaCompactSpace [CompactSpace W] [SecondCountableTopology H]
    [LocallyCompactSpace E] : SigmaCompactSpace (I.interior W) := by
  let : SecondCountableTopology W := ChartedSpace.secondCountable_of_sigmaCompact H W
  let : ChartedSpace E (I.interior W) := (inducedAtlas I).chartedSpace
  let : LocallyCompactSpace (I.interior W) :=
    ChartedSpace.locallyCompactSpace E (I.interior W)
  infer_instance

end ManifoldInterior

/-- A boundaryless model stays boundaryless after changing its model vector space by a
continuous linear equivalence. -/
instance modelWithCorners_boundaryless_transContinuousLinearEquiv
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] (e : E ≃L[ℝ] F) :
    (I.transContinuousLinearEquiv e).Boundaryless where
  range_eq_univ := by
    rw [I.transContinuousLinearEquiv_range e, ModelWithCorners.range_eq_univ, image_univ]
    exact Set.range_eq_univ.mpr e.surjective

/-- The boundaryless Euclidean model used on the interior, expressed with the `Fin n → ℝ`
normed model expected by the Morse-theoretic strip theorems. -/
noncomputable def interiorModel (n : ℕ) :
    ModelWithCorners ℝ (Fin n → ℝ) (EuclideanSpace ℝ (Fin n)) :=
  (𝓘(ℝ, EuclideanSpace ℝ (Fin n))).transContinuousLinearEquiv
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ))

instance interiorModel_boundaryless (n : ℕ) : (interiorModel n).Boundaryless :=
  inferInstanceAs ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).transContinuousLinearEquiv
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ))).Boundaryless

section HalfSpaceInterior

variable {n : ℕ} [NeZero n] {W : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace n) W] [IsManifold (𝓡∂ n) ∞ W]

/-- The usual half-space manifold interior has a smooth atlas with a boundaryless model. -/
theorem interior_isManifold :
    letI := (ManifoldInterior.inducedAtlas (𝓡∂ n) (W := W)).chartedSpace
    IsManifold (interiorModel n) ∞ ((𝓡∂ n).interior W) := by
  let := (ManifoldInterior.inducedAtlas (𝓡∂ n) (W := W)).chartedSpace
  let := (ManifoldInterior.inducedAtlas (𝓡∂ n) (W := W)).isManifold
  unfold interiorModel
  infer_instance

/-- Inclusion of the boundaryless interior into the original manifold is smooth. -/
theorem contMDiff_interior_inclusion :
    letI := (ManifoldInterior.inducedAtlas (𝓡∂ n) (W := W)).chartedSpace
    ContMDiff (interiorModel n) (𝓡∂ n) ∞
      (Subtype.val : (𝓡∂ n).interior W → W) := by
  let := (ManifoldInterior.inducedAtlas (𝓡∂ n) (W := W)).chartedSpace
  unfold interiorModel
  rw [ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left]
  exact (ManifoldInterior.inducedAtlas (𝓡∂ n) (W := W)).contMDiff_subtypeVal

/-- Smoothness into the boundaryless interior is detected in the original half-space
manifold, with no change to the underlying map or topology. -/
theorem contMDiff_into_interior_iff
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    [TopologicalSpace HN] [TopologicalSpace N] [ChartedSpace HN N]
    (J : ModelWithCorners ℝ EN HN) [IsManifold J ∞ N]
    {f : N → (𝓡∂ n).interior W} :
    letI := (ManifoldInterior.inducedAtlas (𝓡∂ n) (W := W)).chartedSpace
    ContMDiff J (interiorModel n) ∞ f ↔
      Continuous f ∧ ContMDiff J (𝓡∂ n) ∞ (fun x => (f x).1) := by
  let := (ManifoldInterior.inducedAtlas (𝓡∂ n) (W := W)).chartedSpace
  unfold interiorModel
  rw [ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right]
  exact (ManifoldInterior.inducedAtlas (𝓡∂ n) (W := W)).contMDiff_iff J

end HalfSpaceInterior

end PoincareHighDim
