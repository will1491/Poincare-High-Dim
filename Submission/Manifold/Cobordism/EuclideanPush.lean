/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth, supported displacements in Euclidean charts

A smooth perturbation of the identity with Lipschitz constant less than one is a
global diffeomorphism. Small compactly supported displacements therefore give
smooth coordinate changes that can push a boundary inward without extending a
manifold's transition functions across its boundary.
-/

namespace PoincareHighDim

open Set Function
open scoped Manifold ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A smooth perturbation of the identity of Lipschitz size less than one is a
global smooth diffeomorphism. -/
noncomputable def perturbationDiffeomorph {g : E → E} {K : ℝ≥0}
    (hg : ContDiff ℝ ∞ g) (hLip : LipschitzWith K g) (hK : K < 1) : E ≃ₘ[ℝ] E := by
  let f : E → E := fun x => x + g x
  have happ : ApproximatesLinearOn f
      ((ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) univ K := by
    apply LipschitzOnWith.approximatesLinearOn
    change LipschitzOnWith K (fun x => x + g x - x) univ
    simpa only [add_sub_cancel_left] using hLip.lipschitzOnWith (s := univ)
  have hsmall : Subsingleton E ∨
      K < ‖((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E)‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial E with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using hK)
  let e : E ≃ₜ E := happ.toHomeomorph f hsmall
  have he : (e : E → E) = f := rfl
  have hf : ContDiff ℝ ∞ (e : E → E) := by
    rw [he]
    exact contDiff_id.add hg
  have hinv : ∀ x : E, ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (e : E → E) (L : E →L[ℝ] E) x := by
    intro x
    have hnorm : ‖fderiv ℝ g x‖ < 1 :=
      (norm_fderiv_le_of_lipschitz ℝ hLip).trans_lt (by exact_mod_cast hK)
    have hu : IsUnit (1 + fderiv ℝ g x) := by
      simpa using (IsUnit.one_sub_of_norm_lt_one (by simpa using hnorm :
        ‖-fderiv ℝ g x‖ < 1))
    obtain ⟨u, hu⟩ := hu
    refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
    rw [he]
    have hd := (hasFDerivAt_id x).add
      ((hg.differentiable (by simp)) x).hasFDerivAt
    change HasFDerivAt (id + g) (u : E →L[ℝ] E) x
    rw [hu]
    exact hd
  exact { toEquiv := e.toEquiv
          contMDiff_toFun := hf.contMDiff
          contMDiff_invFun :=
            (e.contDiff_symm (fun x => Classical.choose_spec (hinv x)) hf).contMDiff }

@[simp] theorem perturbationDiffeomorph_apply {g : E → E} {K : ℝ≥0}
    (hg : ContDiff ℝ ∞ g) (hLip : LipschitzWith K g) (hK : K < 1) (x : E) :
    perturbationDiffeomorph hg hLip hK x = x + g x := rfl

/-- Every smooth compactly supported displacement can be scaled by a positive
constant to give a global diffeomorphism. -/
theorem exists_scaled_perturbationDiffeomorph {g : E → E}
    (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ D : E ≃ₘ[ℝ] E, ∀ x, D x = x + ε • g x := by
  obtain ⟨K, hK⟩ := hg.lipschitzWith_of_hasCompactSupport hs (by simp)
  let ε : ℝ := (2 * ((K : ℝ) + 1))⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  let C : ℝ≥0 := ⟨ε * K, by positivity⟩
  have hC : C < 1 := by
    change ε * (K : ℝ) < 1
    dsimp [ε]
    rw [inv_mul_eq_div]
    apply (div_lt_one (by positivity)).mpr
    linarith [K.coe_nonneg]
  have hLip : LipschitzWith C (fun x => ε • g x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    calc
      ε * ‖g x - g y‖ ≤ ε * ((K : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hK.dist_le_mul x y)
          hε.le
      _ = C * dist x y := by
        change ε * ((K : ℝ) * dist x y) = (ε * (K : ℝ)) * dist x y
        ring
  exact ⟨ε, hε, perturbationDiffeomorph (contDiff_const.smul hg) hLip hC,
    fun _ => rfl⟩

/-- A compactly supported smooth scalar bump displaces points a small distance in
any prescribed direction, by a genuine global diffeomorphism. -/
theorem exists_bump_displacement {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (v : E) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ D : E ≃ₘ[ℝ] E,
      ∀ x, D x = x + (ε * φ x) • v := by
  obtain ⟨ε, hε, D, hD⟩ := exists_scaled_perturbationDiffeomorph
    (hφ.smul contDiff_const) (hs.smul_right (f' := fun _ => v))
  refine ⟨ε, hε, D, fun x => ?_⟩
  have hx := hD x
  change D x = x + ε • (φ x • v) at hx
  simpa only [smul_smul] using hx

omit [CompleteSpace E] in
/-- A bijection fixing the complement of a set preserves that set. -/
theorem diffeomorph_mapsTo_of_eqOn_compl (D : E ≃ₘ[ℝ] E) {s : Set E}
    (hD : EqOn D id sᶜ) : MapsTo D s s := by
  intro x hx
  by_contra h
  have : D (D x) = D x := hD h
  exact h ((D.injective this).symm ▸ hx)

omit [CompleteSpace E] in
/-- Both directions of a supported displacement preserve any region containing
its support. -/
theorem diffeomorph_image_eq_of_eqOn_compl (D : E ≃ₘ[ℝ] E) {s : Set E}
    (hD : EqOn D id sᶜ) : D '' s = s := by
  apply Subset.antisymm (diffeomorph_mapsTo_of_eqOn_compl D hD).image_subset
  intro y hy
  refine ⟨D.symm y, ?_, D.apply_symm_apply y⟩
  by_contra h
  have hfix := hD h
  rw [D.apply_symm_apply] at hfix
  change y = D.symm y at hfix
  exact h (hfix ▸ hy)

/-- In any prescribed coordinate neighborhood one can make a supported smooth
displacement which increases a chosen normal coordinate. A point whose normal
coordinate is unchanged is fixed by the entire displacement. -/
theorem exists_supported_inward_displacement [FiniteDimensional ℝ E]
    {U : Set E} {c : E} (hU : U ∈ nhds c) (ℓ : E →L[ℝ] ℝ) (v : E)
    (hv : 0 < ℓ v) :
    ∃ (K : Set E) (D : E ≃ₘ[ℝ] E),
      IsCompact K ∧ K ⊆ U ∧ EqOn D id Kᶜ ∧
      (∀ x, ℓ x ≤ ℓ (D x)) ∧ ℓ c < ℓ (D c) ∧
      (∀ x, ℓ (D x) = ℓ x → D x = x) := by
  obtain ⟨φ, hK, hs, hφ, hφrange, hφc⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hU
  obtain ⟨ε, hε, D, hD⟩ := exists_bump_displacement hφ hs v
  have hφpos : ∀ x, 0 ≤ φ x := fun x => (hφrange ⟨x, rfl⟩).1
  have hcoord : ∀ x, ℓ (D x) = ℓ x + (ε * φ x) * ℓ v := by
    intro x
    rw [hD, map_add, map_smul, smul_eq_mul]
  refine ⟨tsupport φ, D, hs, hK, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp [hD, image_eq_zero_of_notMem_tsupport hx]
  · intro x
    rw [hcoord]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hε.le (hφpos x)) hv.le)
  · rw [hcoord, hφc, mul_one]
    exact lt_add_of_pos_right _ (mul_pos hε hv)
  · intro x hx
    rw [hcoord] at hx
    have hzero : φ x = 0 := by nlinarith [mul_pos hε hv]
    simp [hD, hzero]

end PoincareHighDim
