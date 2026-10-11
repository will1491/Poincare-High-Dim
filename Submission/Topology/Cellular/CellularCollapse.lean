/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Topology.Cellular.CellCompression
import Submission.Topology.Cellular.CellularShrinking
import Submission.Topology.Cellular.CellularQuotient
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Collapsing a cellular set

A cellular subset of a compact metric space can be collapsed to one point by a continuous
surjection of that space onto itself, with no other identifications. The construction
successively compresses the nested cells and takes the uniform limit of the resulting
homeomorphisms. This is the cellular shrinking step in Brown's proof of Schoenflies.
-/

namespace PoincareHighDim

open Set Metric Filter Topology

namespace ClosedCell

variable {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Transport a closed cell through an ambient homeomorphism. -/
def mapHomeomorph (c : ClosedCell n X) (h : X ≃ₜ Y) : ClosedCell n Y where
  map := h ∘ c.map
  isClosedEmbedding := h.isClosedEmbedding.comp c.isClosedEmbedding
  isOpen_interior := by
    rw [image_comp]
    exact h.isOpenMap _ c.isOpen_interior

@[simp]
theorem mapHomeomorph_carrier (c : ClosedCell n X) (h : X ≃ₜ Y) :
    (c.mapHomeomorph h).carrier = h '' c.carrier := by
  exact range_comp h c.map

@[simp]
theorem mapHomeomorph_interiorSet (c : ClosedCell n X) (h : X ≃ₜ Y) :
    (c.mapHomeomorph h).interiorSet = h '' c.interiorSet := by
  exact image_comp h c.map (diskInterior n)

end ClosedCell

variable {n : ℕ} {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Collapse the intersection of a nested sequence of closed cells, fixing the complement
of the first open cell pointwise. -/
theorem exists_cellular_collapse_of_cells (c : ℕ → ClosedCell n X)
    (hnested : ∀ i, (c (i + 1)).carrier ⊆ (c i).interiorSet) :
    ∃ f : C(X, X), Function.Surjective f ∧
      CollapsesExactly f (⋂ i, (c i).carrier) ∧
      (∀ x ∉ (c 0).interiorSet, f x = x) := by
  classical
  have hnext (i : ℕ) (g : X ≃ₜ X) :
      ∃ g' : X ≃ₜ X,
        (∀ x ∉ (c i).interiorSet, g' x = g x) ∧
        diam (g' '' (c (i + 1)).carrier) ≤ 1 / ((i : ℝ) + 1) := by
    obtain ⟨H, hfix, hsmall⟩ := ((c i).mapHomeomorph g).exists_compression
      (((c (i + 1)).isCompact_carrier).image g.continuous)
      (by simpa only [ClosedCell.mapHomeomorph_interiorSet] using image_mono (hnested i))
      (by positivity : 0 < 1 / ((i : ℝ) + 1))
    refine ⟨g.trans H, ?_, ?_⟩
    · intro x hx
      exact hfix (g x) (by simpa using hx)
    · change diam ((H ∘ g) '' (c (i + 1)).carrier) ≤ _
      rw [image_comp]
      exact hsmall
  choose next hnext_fixed hnext_small using hnext
  let h : ℕ → X ≃ₜ X := fun i => Nat.rec (Homeomorph.refl X) next i
  have hstep : ∀ i x, x ∉ (c i).carrier → h (i + 1) x = h i x := by
    intro i x hx
    exact hnext_fixed i (h i) x (fun hi => hx ((c i).interiorSet_subset_carrier hi))
  have hmono : Antitone (fun i => (c i).carrier) := antitone_nat_of_succ_le
    (fun i => (hnested i).trans (c i).interiorSet_subset_carrier)
  have hfixed : ∀ i j, i ≤ j → ∀ x, x ∉ (c i).carrier → h j x = h i x := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ j hij ih =>
      intro x hx
      rw [hstep j x (fun hxj => hx (hmono hij hxj))]
      exact ih x hx
  have hdiam : Tendsto (fun i => diam (h i '' (c i).carrier)) atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply squeeze_zero (fun i => diam_nonneg)
      (fun i => hnext_small i (h i)) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨f, hsurj, -, hlim_fixed, hfiber⟩ := exists_shrinking_limit
    (fun i => (c i).carrier) h (fun i => (c i).isCompact_carrier) hfixed hdiam
  refine ⟨f, hsurj, hfiber, ?_⟩
  intro x hx
  rw [hlim_fixed 1 x (fun hx1 => hx (hnested 0 hx1))]
  exact hnext_fixed 0 (h 0) x hx

/-- **Cellular collapse.** A cellular set in a compact metric space can be collapsed to one
point by a continuous surjection to the same space, without any other identifications. -/
theorem IsCellular.exists_collapse {K : Set X} (hK : IsCellular n K) :
    ∃ f : C(X, X), Function.Surjective f ∧ CollapsesExactly f K := by
  obtain ⟨c, hnested, rfl⟩ := hK
  obtain ⟨f, hsurj, hfiber, -⟩ := exists_cellular_collapse_of_cells c hnested
  exact ⟨f, hsurj, hfiber⟩

/-- Collapsing a cellular set does not change the homeomorphism type of a compact metric
space. This formulation accepts any continuous surjection with precisely those fibers. -/
theorem IsCellular.nonempty_homeomorph_of_collapsesExactly {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] {K : Set X} (hK : IsCellular n K) {g : X → Y}
    (hg : Continuous g) (hgs : Function.Surjective g) (hgK : CollapsesExactly g K) :
    Nonempty (X ≃ₜ Y) := by
  obtain ⟨f, hfs, hfK⟩ := hK.exists_collapse
  exact PoincareHighDim.nonempty_homeomorph_of_collapsesExactly
    f.continuous hfs hg hgs hfK hgK

end PoincareHighDim
