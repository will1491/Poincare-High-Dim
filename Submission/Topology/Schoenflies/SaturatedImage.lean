/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Open images of saturated subsets

A continuous map from a compact space is a closed map. A saturated open set therefore has
open image wherever that image lies in the ambient interior of the range. This is the
openness fact needed in the cellular argument, without an appeal to invariance of domain.
-/

namespace PoincareHighDim

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] {f : X → Y}

/-- A saturated open set whose image lies in an open subset of the range has open image
in the ambient target. -/
theorem isOpen_image_of_saturated (hf : Continuous f) {U : Set X} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : f '' U ⊆ V) (hVrange : V ⊆ range f)
    (hsat : ∀ x y, f x = f y → x ∈ U → y ∈ U) : IsOpen (f '' U) := by
  have heq : f '' U = V \ f '' Uᶜ := by
    ext y
    constructor
    · rintro hy
      refine ⟨hUV hy, ?_⟩
      obtain ⟨x, hx, rfl⟩ := hy
      rintro ⟨z, hz, hzx⟩
      exact hz (hsat x z hzx.symm hx)
    · rintro ⟨hy, hnot⟩
      obtain ⟨x, rfl⟩ := hVrange hy
      refine ⟨x, ?_, rfl⟩
      by_contra hx
      exact hnot ⟨x, hx, rfl⟩
  rw [heq]
  exact hV.sdiff ((hU.isClosed_compl.isCompact.image hf).isClosed)

/-- It suffices for the image to lie in the interior of the range. -/
theorem isOpen_image_of_saturated_of_subset_interior (hf : Continuous f) {U : Set X}
    (hU : IsOpen U) (hUV : f '' U ⊆ interior (range f))
    (hsat : ∀ x y, f x = f y → x ∈ U → y ∈ U) : IsOpen (f '' U) :=
  isOpen_image_of_saturated hf hU isOpen_interior hUV interior_subset hsat

end PoincareHighDim
