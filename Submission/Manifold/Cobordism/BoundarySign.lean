/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Positive inward derivatives

A positive one-sided derivative provides inward points with strictly larger function
value. This requires differentiability only on the occupied half-ray.
-/

namespace PoincareHighDim
namespace BoundarySign

open Set Filter Topology

/-- A positive right derivative gives strictly increasing values immediately to the right
of the base point. -/
theorem eventually_gt_of_hasDerivWithinAt_pos {f : ℝ → ℝ} {d x : ℝ}
    (hf : HasDerivWithinAt f d (Ici x) x) (hd : 0 < d) :
    ∀ᶠ t in 𝓝[>] x, f x < f t := by
  have hs := (hasDerivWithinAt_iff_tendsto_slope'
    (show x ∉ Ioi x by simp)).mp (hf.mono Ioi_subset_Ici_self)
  filter_upwards [hs.eventually (eventually_gt_nhds hd), self_mem_nhdsWithin]
    with t ht htx
  rw [slope_def_field] at ht
  exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr htx)).mp ht)

/-- A positive inward derivative yields a positive value at an arbitrarily nearby
strictly positive parameter. -/
theorem exists_pos_near_of_hasDerivWithinAt_pos {f : ℝ → ℝ} {d ε : ℝ}
    (hf : HasDerivWithinAt f d (Ici 0) 0) (hd : 0 < d) (hε : 0 < ε) :
    ∃ t, 0 < t ∧ t < ε ∧ f 0 < f t := by
  have hp := eventually_gt_of_hasDerivWithinAt_pos hf hd
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < ε :=
    (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, hft, htε, ht⟩ := (hp.and (he.and self_mem_nhdsWithin)).exists
  exact ⟨t, ht, htε, hft⟩

end BoundarySign
end PoincareHighDim
