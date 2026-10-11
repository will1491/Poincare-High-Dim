/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Topology.Rounded.RoundedCollar
import Submission.Topology.Schoenflies.CollarRescale
import Submission.Morse.Strips.RegularBand
import Submission.Manifold.ModelTransport

/-!
# A bicollar at the equator of the rounded double

A regular zero level on a compact smooth manifold gives a closed collar in its rounded
double, with the last coordinate as collar parameter.
-/

namespace PoincareHighDim.RoundedDouble

open Set Topology
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_equatorial_collar {g : M → ℝ} (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g)
    (hreg : ∀ x, g x = 0 → ¬ IsCriticalPt (𝓡 n) g x) :
    ∃ η : ℝ, 0 < η ∧
      ∃ Ψ : (g ⁻¹' {0}) × Icc (-η) η ≃ₜ boundaryBand g η,
        (∀ p, (Ψ p).1.1.2 = p.2.1) ∧
        ∀ (h : 0 ∈ Icc (-η) η) (x : g ⁻¹' {0}), (Ψ (x, ⟨0, h⟩)).1.1 = (x.1, 0) := by
  have hg' := contMDiff_morseModelI_iff.mpr hg
  have h := exists_regular_level_collar hg' (c := 0) (by
    intro x hx
    rw [isCriticalPt_morseModelI_iff hg]
    exact hreg x hx)
  obtain ⟨δ, hδ, Φ, hΦ, hΦ0⟩ := h
  let A : Icc (-δ) δ ≃ₜ Icc (0 - δ) (0 + δ) :=
    Homeomorph.setCongr (by simp only [zero_sub, zero_add])
  let B : (g ⁻¹' Icc (0 - δ) (0 + δ)) ≃ₜ (g ⁻¹' Icc (-δ) δ) :=
    Homeomorph.setCongr (by simp only [zero_sub, zero_add])
  let Φ' := (Homeomorph.prodCongr (Homeomorph.refl (g ⁻¹' {0})) A).trans (Φ.trans B)
  have hΦ' (p : (g ⁻¹' {0}) × Icc (-δ) δ) : g (Φ' p).1 = p.2.1 :=
    hΦ (p.1, A p.2)
  have hΦ0' (h : 0 ∈ Icc (-δ) δ) (x : g ⁻¹' {0}) :
      (Φ' (x, ⟨0, h⟩)).1 = x.1 := hΦ0 (by simpa only [zero_sub, zero_add] using h) x
  have hη : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hηδ : Real.sqrt δ ^ 2 ≤ δ := (Real.sq_sqrt hδ.le).le
  refine ⟨Real.sqrt δ, hη, boundaryBandHomeomorph hη.le hηδ Φ' hΦ',
    boundaryBandHomeomorph_height hη.le hηδ Φ' hΦ', ?_⟩
  intro h x
  exact boundaryBandHomeomorph_zero hη.le hηδ Φ' hΦ' hΦ0' x

/-- Normalize the equatorial collar to the parameter interval `[-1,1]`. -/
theorem exists_unit_equatorial_collar {g : M → ℝ}
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g)
    (hreg : ∀ x, g x = 0 → ¬ IsCriticalPt (𝓡 n) g x) :
    ∃ η : ℝ, 0 < η ∧
      ∃ Ψ : (g ⁻¹' {0}) × Icc (-1 : ℝ) 1 ≃ₜ
          {p : boundary g // p.1.2 / η ∈ Icc (-1 : ℝ) 1},
        ∀ p, (Ψ p).1.1.2 / η = p.2.1 := by
  obtain ⟨η, hη, Φ, hΦ, -⟩ := exists_equatorial_collar hg hreg
  exact ⟨η, hη, rescaleHeightCollar hη (fun p : boundary g => p.1.2) Φ,
    rescaleHeightCollar_height hη _ Φ hΦ⟩

end PoincareHighDim.RoundedDouble
