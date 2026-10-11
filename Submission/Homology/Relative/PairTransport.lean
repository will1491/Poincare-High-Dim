/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Homology.Relative.DeltaIso

/-!
# Transporting the homological cobordism hypothesis

A homeomorphism of pairs preserves the vanishing of integral relative homology.
This permits the hypothesis on an abstract cobordism to be transferred to a strip
presentation without replacing it by a stronger homotopy-equivalence assumption.
-/

namespace PoincareHighDim

open SingularPair

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Relative homology vanishing is preserved by a homeomorphism of pairs. -/
theorem RelHomologyVanishes.homeomorph {A : Set X} {B : Set Y}
    (h : RelHomologyVanishes X A) (e : X ≃ₜ Y) (he : e '' A = B) :
    RelHomologyVanishes Y B :=
  fun k => (h k).of_iso (HrelIsoOfHomeomorphImage Z e he k).symm

/-- Membership correspondence is sufficient to transfer the relative homology hypothesis. -/
theorem RelHomologyVanishes.homeomorph_of_mem_iff {A : Set X} {B : Set Y}
    (h : RelHomologyVanishes X A) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B) :
    RelHomologyVanishes Y B :=
  fun k => (h k).of_iso (HrelIsoOfHomeomorphIff Z e he k).symm

end PoincareHighDim
