/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.SignedCover
import Submission.Manifold.Cobordism.AmbientCollar

/-! # Local defining functions from signed product charts -/

namespace PoincareHighDim
namespace StripFunction.LocalBoundaryFunction

open Set Topology Filter
open scoped Manifold ContDiff

variable {E H M F G V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
    [IsManifold I ∞ M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    [TopologicalSpace V] [ChartedSpace G V] {J : ModelWithCorners ℝ F G}
    [IsManifold J ∞ V]

/-- Once a product chart identifies the occupied half-space and its zero slice, its inverse
height is a local boundary function. Moving in its last coordinate supplies every inward
curve required by the partition construction. -/
noncomputable def ofPartialDiffeomorph {S B : Set M} {b : M}
    (Φ : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) I (V × ℝ) M ∞)
    (hb : b ∈ Φ.target)
    (hside : ∀ x ∈ Φ.target, x ∈ S ↔ 0 ≤ (Φ.symm x).2)
    (hzero : ∀ x ∈ Φ.target, x ∈ B ↔ (Φ.symm x).2 = 0) :
    StripFunction.LocalBoundaryFunction I S B b where
  domain := Φ.target
  open_domain := Φ.open_target
  mem_domain := hb
  value x := (Φ.symm x).2
  smooth := AmbientCollar.contMDiffOn_normalCoordinate Φ
  side := hside
  zero := hzero
  inward x hx hxB := by
    let z := Φ.symm x
    have hz : z ∈ Φ.source := Φ.map_target hx
    have hz0 : z.2 = 0 := (hzero x hx).mp hxB
    have hzbase : (z.1, (0 : ℝ)) ∈ Φ.source := by simpa only [← hz0] using hz
    let γ : ℝ → M := fun t => Φ (z.1, t)
    have hp : ContMDiff 𝓘(ℝ, ℝ) (J.prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (z.1, t)) :=
      contMDiff_const.prodMk contMDiff_id
    have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ 0 :=
      (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hzbase)).comp 0 hp.contMDiffAt
    have hγ0 : γ 0 = x := by
      change Φ (z.1, 0) = x
      rw [← hz0]
      exact Φ.right_inv hx
    have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), (z.1, t) ∈ Φ.source :=
      hp.continuous.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hzbase)
    have hcoord : (fun t => (Φ.symm (γ t)).2) =ᶠ[𝓝 (0 : ℝ)] id := by
      filter_upwards [hevent] with t ht
      exact congrArg Prod.snd (Φ.left_inv ht)
    refine ⟨γ, 1, hγ, hγ0, ?_, ?_, zero_lt_one⟩
    · filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with t ht ht0
      apply (hside (γ t) (Φ.map_source ht)).mpr
      change 0 ≤ (Φ.symm (Φ (z.1, t))).2
      have heq : (Φ.symm (Φ (z.1, t))).2 = t := congrArg Prod.snd (Φ.left_inv ht)
      exact heq.symm ▸ ht0
    · exact (hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq hcoord

end StripFunction.LocalBoundaryFunction
end PoincareHighDim
