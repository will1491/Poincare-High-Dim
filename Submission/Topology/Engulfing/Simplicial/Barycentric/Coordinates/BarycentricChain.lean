/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic

/-!
# Geometry of barycentric face chains

The vertices of a barycentric simplex are the centroids of a chain of nonempty faces.
-/

namespace PoincareHighDim.Engulfing

set_option linter.unusedSectionVars false

open Set
open scoped BigOperators

variable {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]

/-- A finite chain of nonempty faces, ordered by inclusion. The chain itself may be empty. -/
def IsFaceChain (C : Finset (Finset ι)) : Prop :=
  (∀ s ∈ C, s.Nonempty) ∧ ∀ s ∈ C, ∀ t ∈ C, s ⊆ t ∨ t ⊆ s

theorem IsFaceChain.mono {C D : Finset (Finset ι)} (hC : IsFaceChain C) (hDC : D ⊆ C) :
    IsFaceChain D :=
  ⟨fun s hs => hC.1 s (hDC hs), fun s hs t ht => hC.2 s (hDC hs) t (hDC ht)⟩

/-- Every nonempty finite face chain has a largest member. -/
theorem IsFaceChain.exists_largest {C : Finset (Finset ι)} (hC : IsFaceChain C)
    (hCne : C.Nonempty) : ∃ s ∈ C, ∀ t ∈ C, t ⊆ s := by
  obtain ⟨s, hs, hmax⟩ := C.exists_max_image Finset.card hCne
  refine ⟨s, hs, fun t ht => ?_⟩
  rcases hC.2 t ht s hs with hts | hst
  · exact hts
  · exact (Finset.eq_of_subset_of_card_le hst (hmax t ht)).symm.subset

/-- A face in a finite chain has a vertex missing from every strictly smaller face. -/
theorem IsFaceChain.exists_exclusive_vertex {C : Finset (Finset ι)} (hC : IsFaceChain C)
    {s : Finset ι} (hs : s ∈ C) :
    ∃ i ∈ s, ∀ t ∈ C, t ⊆ s → i ∈ t → t = s := by
  classical
  let D := C.filter (fun t => t ⊆ s ∧ t ≠ s)
  by_cases hD : D.Nonempty
  · obtain ⟨r, hr, hrmax⟩ := (hC.mono (Finset.filter_subset _ C)).exists_largest hD
    have hrs : r ⊆ s := (Finset.mem_filter.mp hr).2.1
    have hrsne : r ≠ s := (Finset.mem_filter.mp hr).2.2
    have hsr : ¬ s ⊆ r := fun h => hrsne (Finset.Subset.antisymm hrs h)
    obtain ⟨i, his, hir⟩ := Finset.not_subset.mp hsr
    refine ⟨i, his, fun t ht hts hit => ?_⟩
    by_contra hne
    exact hir (hrmax t (Finset.mem_filter.mpr ⟨ht, hts, hne⟩) hit)
  · obtain ⟨i, hi⟩ := hC.1 s hs
    refine ⟨i, hi, fun t ht hts _ => ?_⟩
    by_contra hne
    exact hD ⟨t, Finset.mem_filter.mpr ⟨ht, hts, hne⟩⟩

/-- A centroid cannot lie in the span of faces missing one of its vertices. -/
theorem centroid_notMem_affineSpan {v : ι → E} (hv : AffineIndependent ℝ v)
    {s t : Finset ι} (hs : s.Nonempty) {i : ι} (his : i ∈ s) (hit : i ∉ t) :
    s.centroid ℝ v ∉ affineSpan ℝ (v '' (t : Set ι)) := by
  intro hm
  have hz := hv.eq_zero_of_affineCombination_mem_affineSpan
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) hm his hit
  change (s.card : ℝ)⁻¹ = 0 at hz
  exact (inv_ne_zero (by exact_mod_cast (Finset.card_pos.mpr hs).ne')) hz

/-- Distinct nonempty faces of an independent vertex family have distinct centroids. -/
theorem centroid_injective_of_affineIndependent {v : ι → E} (hv : AffineIndependent ℝ v)
    {s t : Finset ι} (hs : s.Nonempty) (ht : t.Nonempty)
    (heq : s.centroid ℝ v = t.centroid ℝ v) : s = t := by
  apply Finset.Subset.antisymm
  · intro i hi
    by_contra hit
    apply centroid_notMem_affineSpan hv hs hi hit
    rw [heq]
    exact affineCombination_mem_affineSpan_image
      (t.sum_centroidWeights_eq_one_of_nonempty ℝ ht) (fun _ hi hn => (hn hi).elim) v
  · intro i hi
    by_contra his
    apply centroid_notMem_affineSpan hv ht hi his
    rw [← heq]
    exact affineCombination_mem_affineSpan_image
      (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) (fun _ hi hn => (hn hi).elim) v

/-- The centroids of a finite chain of nonempty faces of independent vertices are affinely
independent. -/
theorem IsFaceChain.affineIndependent_centroids {v : ι → E} (hv : AffineIndependent ℝ v)
    {C : Finset (Finset ι)} (hC : IsFaceChain C) :
    AffineIndependent ℝ (fun s : C => s.1.centroid ℝ v) := by
  classical
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    by_cases hCne : C.Nonempty
    · obtain ⟨s, hs, hmax⟩ := hC.exists_largest hCne
      obtain ⟨i, his, hi⟩ := hC.exists_exclusive_vertex hs
      have hprev := ih (C.erase s) (Finset.erase_ssubset hs)
        (hC.mono (Finset.erase_subset s C))
      let j : C := ⟨s, hs⟩
      let f : {z : C // z ≠ j} ↪ C.erase s := {
        toFun := fun z => ⟨z.1.1, Finset.mem_erase.mpr
          ⟨fun h => z.2 (Subtype.ext h), z.1.2⟩⟩
        inj' := fun x y h => Subtype.ext (Subtype.ext
          (congrArg (fun z : C.erase s => (z : Finset ι)) h)) }
      have hsub : AffineIndependent ℝ
          (fun z : {z : C // z ≠ j} => z.1.1.centroid ℝ v) := hprev.comp_embedding f
      apply hsub.affineIndependent_of_notMem_span
      intro hm
      apply centroid_notMem_affineSpan hv (hC.1 s hs) his (Finset.notMem_erase i s)
      apply (affineSpan_le.mpr ?_) hm
      rintro _ ⟨t, ht, rfl⟩
      have hti : i ∉ (t : Finset ι) := fun hit => ht (Subtype.ext (hi t t.2 (hmax t t.2) hit))
      have hts : (t : Finset ι) ⊆ s.erase i := fun x hx =>
        Finset.mem_erase.mpr ⟨fun h => hti (h ▸ hx), hmax t t.2 hx⟩
      exact affineSpan_mono ℝ (image_mono hts)
        (affineCombination_mem_affineSpan_image
          (t.1.sum_centroidWeights_eq_one_of_nonempty ℝ (hC.1 t t.2))
          (fun _ hi hn => (hn hi).elim) v)
    · have hCe : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCne
      subst C
      exact affineIndependent_of_subsingleton ℝ _

end PoincareHighDim.Engulfing
