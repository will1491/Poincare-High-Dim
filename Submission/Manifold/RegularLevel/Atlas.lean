/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Restricting charts to corresponding subspaces

An ambient chart restricts to a chart between two subspaces whenever it identifies
their intersections with its source and target. The subspaces need not be open.
This is the topological construction used for regular-level and boundary charts.
-/

open Set Topology

namespace OpenPartialHomeomorph.IsImage

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : OpenPartialHomeomorph X Y} {s : Set X} {t : Set Y}

/-- Restriction of an ambient chart to a pair of corresponding subspaces. -/
noncomputable def subtype (h : e.IsImage s t) [Nonempty s] [Nonempty t] :
    OpenPartialHomeomorph s t := by
  classical
  let F : s → t := fun x => if hx : e x ∈ t then ⟨e x, hx⟩ else Classical.arbitrary t
  let G : t → s := fun y => if hy : e.symm y ∈ s then ⟨e.symm y, hy⟩ else Classical.arbitrary s
  have hF (x : s) (hx : x.1 ∈ e.source) : (F x).1 = e x := by
    simp only [F, dite_eq_left ((h hx).2 x.2)]
  have hG (y : t) (hy : y.1 ∈ e.target) : (G y).1 = e.symm y := by
    simp only [G, dite_eq_left ((h.symm hy).2 y.2)]
  refine
    { toFun := F
      invFun := G
      source := Subtype.val ⁻¹' e.source
      target := Subtype.val ⁻¹' e.target
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := e.open_target.preimage continuous_subtype_val
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_ }
  · intro x hx
    change (F x).1 ∈ e.target
    rw [hF x hx]
    exact e.map_source hx
  · intro y hy
    change (G y).1 ∈ e.source
    rw [hG y hy]
    exact e.map_target hy
  · intro x hx
    apply Subtype.ext
    rw [hG (F x) (by rw [hF x hx]; exact e.map_source hx), hF x hx]
    exact e.left_inv hx
  · intro y hy
    apply Subtype.ext
    rw [hF (G y) (by rw [hG y hy]; exact e.map_target hy), hG y hy]
    exact e.right_inv hy
  · apply continuousOn_iff_continuous_domRestrict.mpr
    apply continuous_induced_rng.mpr
    have he : ContinuousOn (fun x : s => e x) (Subtype.val ⁻¹' e.source) :=
      e.continuousOn.comp continuous_subtype_val.continuousOn
      (fun x hx => hx)
    have hEq : EqOn (fun x : s => (F x).1) (fun x : s => e x)
        (Subtype.val ⁻¹' e.source) := hF
    exact continuousOn_iff_continuous_domRestrict.mp (he.congr hEq)
  · apply continuousOn_iff_continuous_domRestrict.mpr
    apply continuous_induced_rng.mpr
    have he : ContinuousOn (fun y : t => e.symm y) (Subtype.val ⁻¹' e.target) :=
      e.continuousOn_symm.comp continuous_subtype_val.continuousOn
      (fun y hy => hy)
    have hEq : EqOn (fun y : t => (G y).1) (fun y : t => e.symm y)
        (Subtype.val ⁻¹' e.target) := hG
    exact continuousOn_iff_continuous_domRestrict.mp (he.congr hEq)

@[simp] theorem subtype_source (h : e.IsImage s t) [Nonempty s] [Nonempty t] :
    h.subtype.source = Subtype.val ⁻¹' e.source := rfl

@[simp] theorem subtype_target (h : e.IsImage s t) [Nonempty s] [Nonempty t] :
    h.subtype.target = Subtype.val ⁻¹' e.target := rfl

theorem subtype_apply_val (h : e.IsImage s t) [Nonempty s] [Nonempty t]
    {x : s} (hx : x.1 ∈ e.source) : (h.subtype x).1 = e x := by
  classical
  change (if hx : e x ∈ t then (⟨e x, hx⟩ : t) else Classical.arbitrary t).1 = e x
  rw [dite_eq_left ((h hx).2 x.2)]

theorem subtype_symm_apply_val (h : e.IsImage s t) [Nonempty s] [Nonempty t]
    {y : t} (hy : y.1 ∈ e.target) : (h.subtype.symm y).1 = e.symm y := by
  classical
  change (if hy : e.symm y ∈ s then (⟨e.symm y, hy⟩ : s) else Classical.arbitrary s).1 = e.symm y
  rw [dite_eq_left ((h.symm hy).2 y.2)]

end OpenPartialHomeomorph.IsImage
