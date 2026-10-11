/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Morse.Strips.RegularBand
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Smooth product coordinates on a regular compact band

The product coordinates supplied by the unit-speed flow are smooth for manifold structures
on the level and the band whose inclusions into the ambient manifold are smooth immersions.
This compatibility condition concerns the given smooth structures; neither structure is
defined by transporting the product structure through the resulting homeomorphism.
-/

namespace PoincareHighDim

open Set Topology Manifold
open scoped Manifold ContDiff

/-- Affine rescaling is a diffeomorphism of closed intervals with their usual manifold
structures, including their boundary points. -/
noncomputable def intervalDiffeomorph (a b : ℝ) [Fact (a < b)] :
    Icc a b ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1 :=
  { (iccHomeoI a b Fact.out).toEquiv with
    contMDiff_toFun := by
      rw [contMDiff_iff_comp_subtypeVal_Icc]
      refine ⟨(iccHomeoI a b Fact.out).continuous, ?_⟩
      change ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
        (fun x : Icc a b => (x.1 - a) / (b - a))
      simp only [div_eq_mul_inv]
      exact (contMDiff_subtypeVal_Icc.sub contMDiff_const).mul contMDiff_const
    contMDiff_invFun := by
      rw [contMDiff_iff_comp_subtypeVal_Icc]
      refine ⟨(iccHomeoI a b Fact.out).symm.continuous, ?_⟩
      change ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
        (fun x : Icc (0 : ℝ) 1 => (b - a) * x.1 + a)
      exact (contMDiff_const.mul contMDiff_subtypeVal_Icc).add contMDiff_const }

@[simp] theorem intervalDiffeomorph_apply_coe (a b : ℝ) [Fact (a < b)]
    (x : Icc a b) : (intervalDiffeomorph a b x).1 = (x.1 - a) / (b - a) := rfl

@[simp] theorem intervalDiffeomorph_symm_apply_coe (a b : ℝ) [Fact (a < b)]
    (x : Icc (0 : ℝ) 1) : ((intervalDiffeomorph a b).symm x).1 = (b - a) * x.1 + a := rfl

/-- Equal subsets with smooth structures induced by immersion into the same ambient
manifold are diffeomorphic by the identity on their ambient points. -/
noncomputable def immersedSetCongr
    {E E₀ E₁ H H₀ H₁ M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H] [TopologicalSpace H₀] [TopologicalSpace H₁]
    [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)
    (I₀ : ModelWithCorners ℝ E₀ H₀) (I₁ : ModelWithCorners ℝ E₁ H₁)
    {S T : Set M} [ChartedSpace H₀ S] [ChartedSpace H₁ T]
    [IsManifold I₀ ∞ S] [IsManifold I₁ ∞ T]
    (hS : IsImmersion I₀ I ∞ (Subtype.val : S → M))
    (hT : IsImmersion I₁ I ∞ (Subtype.val : T → M)) (hST : S = T) :
    S ≃ₘ⟮I₀, I₁⟯ T :=
  { (Homeomorph.setCongr hST).toEquiv with
    contMDiff_toFun := by
      rw [ContMDiff.iff_comp_isImmersion hT]
      exact ⟨(Homeomorph.setCongr hST).continuous, hS.contMDiff⟩
    contMDiff_invFun := by
      rw [ContMDiff.iff_comp_isImmersion hS]
      exact ⟨(Homeomorph.setCongr hST).symm.continuous, hT.contMDiff⟩ }

@[simp] theorem immersedSetCongr_apply_val
    {E E₀ E₁ H H₀ H₁ M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H] [TopologicalSpace H₀] [TopologicalSpace H₁]
    [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)
    (I₀ : ModelWithCorners ℝ E₀ H₀) (I₁ : ModelWithCorners ℝ E₁ H₁)
    {S T : Set M} [ChartedSpace H₀ S] [ChartedSpace H₁ T]
    [IsManifold I₀ ∞ S] [IsManifold I₁ ∞ T]
    (hS : IsImmersion I₀ I ∞ (Subtype.val : S → M))
    (hT : IsImmersion I₁ I ∞ (Subtype.val : T → M)) (hST : S = T) (x : S) :
    (immersedSetCongr I I₀ I₁ hS hT hST x).1 = x.1 := rfl

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- A compact band without critical points is smoothly a product whenever its given
manifold structures, and that of the chosen level, are compatible with their ambient
inclusions. Smooth maps lift from the ambient manifold to the given level and band
structures, including at the band's boundary. -/
theorem exists_regular_band_diffeomorph_of_lifting
    {E₀ E₁ H₀ H₁ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H₀] [TopologicalSpace H₁]
    (I₀ : ModelWithCorners ℝ E₀ H₀) (I₁ : ModelWithCorners ℝ E₁ H₁)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {a b c : ℝ} [Fact (a < b)] (hc : c ∈ Icc a b)
    [ChartedSpace H₀ (f ⁻¹' {c})] [ChartedSpace H₁ (f ⁻¹' Icc a b)]
    [IsManifold I₀ ∞ (f ⁻¹' {c})] [IsManifold I₁ ∞ (f ⁻¹' Icc a b)]
    (hlevel : ContMDiff I₀ I ∞ (Subtype.val : (f ⁻¹' {c}) → M))
    (hband : ContMDiff I₁ I ∞ (Subtype.val : (f ⁻¹' Icc a b) → M))
    (hliftlevel : ∀ k : (f ⁻¹' Icc a b) → (f ⁻¹' {c}), Continuous k →
      ContMDiff I₁ I ∞ (fun x => (k x).1) → ContMDiff I₁ I₀ ∞ k)
    (hliftband : ∀ k : (f ⁻¹' {c}) × Icc a b → (f ⁻¹' Icc a b), Continuous k →
      ContMDiff (I₀.prod (𝓡∂ 1)) I ∞ (fun x => (k x).1) →
      ContMDiff (I₀.prod (𝓡∂ 1)) I₁ ∞ k)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x ∈ Icc a b → ¬ IsCriticalPt I f x) :
    ∃ Φ : ((f ⁻¹' {c}) × Icc a b) ≃ₘ⟮I₀.prod (𝓡∂ 1), I₁⟯ (f ⁻¹' Icc a b),
      (∀ p, f (Φ p).1 = p.2.1) ∧
      ∀ x : f ⁻¹' {c}, (Φ (x, ⟨c, hc⟩)).1 = x.1 := by
  classical
  have hab : a < b := Fact.out
  have hM : MorseStrip I f a b :=
    { smooth := hf
      lt := hab
      compact := hcompact
      regular := by
        intro x hx
        apply hreg x
        rcases hx with hx | hx <;> rw [hx]
        · exact ⟨le_rfl, hab.le⟩
        · exact ⟨hab.le, le_rfl⟩
      nondegenerate := fun x hx hcrit => (hreg x ⟨hx.1.le, hx.2.le⟩ hcrit).elim }
  obtain ⟨D, -, -, -⟩ := exists_gradientLikeStrip hM le_rfl hab le_rfl hM.regular
    (∅ : Finset M) (by
      intro x
      simp only [Finset.notMem_empty, false_iff, not_and]
      exact fun hx => hreg x ⟨hx.1.le, hx.2.le⟩) (R₀ := 1) zero_lt_one
  have htransport (x : M) (hx : f x ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) :
      f (D.flow (f x - t) x) = t := by
    have h := D.f_flow_eq_sub_of_levels hf (T := f x - t) hx
      (by simpa only [sub_sub_cancel] using ht)
      (by intro y hy p hp; exact (Finset.notMem_empty p hp).elim)
      (f x - t) right_mem_uIcc
    simpa only [sub_sub_cancel] using h
  let F : (f ⁻¹' {c}) × Icc a b → (f ⁻¹' Icc a b) := fun p =>
    ⟨D.flow (c - p.2.1) p.1.1, by
      have hx : f p.1.1 = c := p.1.2
      have ht := htransport p.1.1 (by rwa [hx]) p.2.1 p.2.2
      rw [hx] at ht
      change f (D.flow (c - p.2.1) p.1.1) ∈ Icc a b
      rw [ht]
      exact p.2.2⟩
  let G : (f ⁻¹' Icc a b) → (f ⁻¹' {c}) × Icc a b := fun x =>
    (⟨D.flow (f x.1 - c) x.1, htransport x.1 x.2 c hc⟩, ⟨f x.1, x.2⟩)
  have hF (p : (f ⁻¹' {c}) × Icc a b) : f (F p).1 = p.2.1 := by
    have hx : f p.1.1 = c := p.1.2
    have ht := htransport p.1.1 (by rwa [hx]) p.2.1 p.2.2
    simpa only [F, hx] using ht
  have hGF (p : (f ⁻¹' {c}) × Icc a b) : G (F p) = p := by
    apply Prod.ext
    · apply Subtype.ext
      change D.flow (f (F p).1 - c) (D.flow (c - p.2.1) p.1.1) = p.1.1
      rw [hF, D.flow_flow]
      simp only [sub_add_sub_cancel, sub_self, D.flow_zero]
    · exact Subtype.ext (hF p)
  have hFG (x : f ⁻¹' Icc a b) : F (G x) = x := by
    apply Subtype.ext
    change D.flow (c - f x.1) (D.flow (f x.1 - c) x.1) = x.1
    rw [D.flow_flow]
    simp only [sub_add_sub_cancel, sub_self, D.flow_zero]
  have hFcont : Continuous F := by
    apply Continuous.subtype_mk
    exact D.continuous_flow_joint.comp
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).prodMk
        (continuous_subtype_val.comp continuous_fst))
  have hGcont : Continuous G := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact D.continuous_flow_joint.comp
        (((hf.continuous.comp continuous_subtype_val).sub continuous_const).prodMk
          continuous_subtype_val)
    · exact (hf.continuous.comp continuous_subtype_val).subtype_mk _
  have hFsmooth : ContMDiff (I₀.prod (𝓡∂ 1)) I₁ ∞ F := by
    apply hliftband F hFcont
    exact D.contMDiff_flow_joint.comp
      ((contMDiff_const.sub (contMDiff_subtypeVal_Icc.comp contMDiff_snd)).prodMk
        (hlevel.comp contMDiff_fst))
  have hGsmooth : ContMDiff I₁ (I₀.prod (𝓡∂ 1)) ∞ G := by
    apply ContMDiff.prodMk
    · apply hliftlevel (fun x => (G x).1) (continuous_fst.comp hGcont)
      exact D.contMDiff_flow_joint.comp
        (((hf.comp hband).sub contMDiff_const).prodMk hband)
    · rw [contMDiff_iff_comp_subtypeVal_Icc]
      exact ⟨continuous_snd.comp hGcont, hf.comp hband⟩
  let Φ : ((f ⁻¹' {c}) × Icc a b) ≃ₘ⟮I₀.prod (𝓡∂ 1), I₁⟯ (f ⁻¹' Icc a b) :=
    { toFun := F
      invFun := G
      left_inv := hGF
      right_inv := hFG
      contMDiff_toFun := hFsmooth
      contMDiff_invFun := hGsmooth }
  refine ⟨Φ, hF, ?_⟩
  intro x
  change D.flow (c - c) x.1 = x.1
  rw [sub_self, D.flow_zero]

/-- Smooth-immersion compatibility supplies the lifting properties in the regular-band
product theorem. -/
theorem exists_regular_band_diffeomorph
    {E₀ E₁ H₀ H₁ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H₀] [TopologicalSpace H₁]
    (I₀ : ModelWithCorners ℝ E₀ H₀) (I₁ : ModelWithCorners ℝ E₁ H₁)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {a b c : ℝ} [Fact (a < b)] (hc : c ∈ Icc a b)
    [ChartedSpace H₀ (f ⁻¹' {c})] [ChartedSpace H₁ (f ⁻¹' Icc a b)]
    [IsManifold I₀ ∞ (f ⁻¹' {c})] [IsManifold I₁ ∞ (f ⁻¹' Icc a b)]
    (hlevel : IsImmersion I₀ I ∞ (Subtype.val : (f ⁻¹' {c}) → M))
    (hband : IsImmersion I₁ I ∞ (Subtype.val : (f ⁻¹' Icc a b) → M))
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x ∈ Icc a b → ¬ IsCriticalPt I f x) :
    ∃ Φ : ((f ⁻¹' {c}) × Icc a b) ≃ₘ⟮I₀.prod (𝓡∂ 1), I₁⟯ (f ⁻¹' Icc a b),
      (∀ p, f (Φ p).1 = p.2.1) ∧
      ∀ x : f ⁻¹' {c}, (Φ (x, ⟨c, hc⟩)).1 = x.1 := by
  apply exists_regular_band_diffeomorph_of_lifting I₀ I₁ hf hc hlevel.contMDiff
    hband.contMDiff ?_ ?_ hcompact hreg
  · intro k hk hs
    exact (ContMDiff.iff_comp_isImmersion hlevel).mpr ⟨hk, hs⟩
  · intro k hk hs
    exact (ContMDiff.iff_comp_isImmersion hband).mpr ⟨hk, hs⟩

/-- The regular-band product theorem with the unit interval as parameter and with the
incoming end fixed pointwise. All smooth structures are supplied in advance and checked
against their ambient inclusions. -/
theorem exists_regular_band_unitInterval_diffeomorph_of_lifting
    {E₀ E₁ H₀ H₁ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H₀] [TopologicalSpace H₁]
    (I₀ : ModelWithCorners ℝ E₀ H₀) (I₁ : ModelWithCorners ℝ E₁ H₁)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} [Fact (a < b)]
    [ChartedSpace H₀ (f ⁻¹' {a})] [ChartedSpace H₁ (f ⁻¹' Icc a b)]
    [IsManifold I₀ ∞ (f ⁻¹' {a})] [IsManifold I₁ ∞ (f ⁻¹' Icc a b)]
    (hlevel : ContMDiff I₀ I ∞ (Subtype.val : (f ⁻¹' {a}) → M))
    (hband : ContMDiff I₁ I ∞ (Subtype.val : (f ⁻¹' Icc a b) → M))
    (hliftlevel : ∀ k : (f ⁻¹' Icc a b) → (f ⁻¹' {a}), Continuous k →
      ContMDiff I₁ I ∞ (fun x => (k x).1) → ContMDiff I₁ I₀ ∞ k)
    (hliftband : ∀ k : (f ⁻¹' {a}) × Icc a b → (f ⁻¹' Icc a b), Continuous k →
      ContMDiff (I₀.prod (𝓡∂ 1)) I ∞ (fun x => (k x).1) →
      ContMDiff (I₀.prod (𝓡∂ 1)) I₁ ∞ k)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x ∈ Icc a b → ¬ IsCriticalPt I f x) :
    ∃ Φ : ((f ⁻¹' {a}) × Icc (0 : ℝ) 1) ≃ₘ⟮I₀.prod (𝓡∂ 1), I₁⟯
        (f ⁻¹' Icc a b),
      (∀ p, f (Φ p).1 = (b - a) * p.2.1 + a) ∧
      (∀ x : f ⁻¹' {a}, (Φ (x, 0)).1 = x.1) ∧
      (∀ x : f ⁻¹' {a}, f (Φ (x, 1)).1 = b) := by
  have hab : a < b := Fact.out
  obtain ⟨Ψ, hΨ, hΨa⟩ := exists_regular_band_diffeomorph_of_lifting I₀ I₁ hf
    (left_mem_Icc.mpr hab.le) hlevel hband hliftlevel hliftband hcompact hreg
  let Φ := ((Diffeomorph.refl I₀ (f ⁻¹' {a}) ∞).prodCongr
    (intervalDiffeomorph a b).symm).trans Ψ
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro p
    exact hΨ (p.1, (intervalDiffeomorph a b).symm p.2)
  · intro x
    change (Ψ (x, (intervalDiffeomorph a b).symm 0)).1 = x.1
    have hz : (intervalDiffeomorph a b).symm 0 = ⟨a, left_mem_Icc.mpr hab.le⟩ := by
      apply Subtype.ext
      simp
    rw [hz]
    exact hΨa x
  · intro x
    have h := hΨ (x, (intervalDiffeomorph a b).symm 1)
    change f (Ψ (x, (intervalDiffeomorph a b).symm 1)).1 = b
    rw [h, intervalDiffeomorph_symm_apply_coe]
    change (b - a) * 1 + a = b
    ring

/-- The unit-interval product theorem for given level and band structures whose ambient
inclusions are smooth immersions. -/
theorem exists_regular_band_unitInterval_diffeomorph
    {E₀ E₁ H₀ H₁ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H₀] [TopologicalSpace H₁]
    (I₀ : ModelWithCorners ℝ E₀ H₀) (I₁ : ModelWithCorners ℝ E₁ H₁)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} [Fact (a < b)]
    [ChartedSpace H₀ (f ⁻¹' {a})] [ChartedSpace H₁ (f ⁻¹' Icc a b)]
    [IsManifold I₀ ∞ (f ⁻¹' {a})] [IsManifold I₁ ∞ (f ⁻¹' Icc a b)]
    (hlevel : IsImmersion I₀ I ∞ (Subtype.val : (f ⁻¹' {a}) → M))
    (hband : IsImmersion I₁ I ∞ (Subtype.val : (f ⁻¹' Icc a b) → M))
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x ∈ Icc a b → ¬ IsCriticalPt I f x) :
    ∃ Φ : ((f ⁻¹' {a}) × Icc (0 : ℝ) 1) ≃ₘ⟮I₀.prod (𝓡∂ 1), I₁⟯
        (f ⁻¹' Icc a b),
      (∀ p, f (Φ p).1 = (b - a) * p.2.1 + a) ∧
      (∀ x : f ⁻¹' {a}, (Φ (x, 0)).1 = x.1) ∧
      (∀ x : f ⁻¹' {a}, f (Φ (x, 1)).1 = b) := by
  apply exists_regular_band_unitInterval_diffeomorph_of_lifting I₀ I₁ hf hlevel.contMDiff
    hband.contMDiff ?_ ?_ hcompact hreg
  · intro k hk hs
    exact (ContMDiff.iff_comp_isImmersion hlevel).mpr ⟨hk, hs⟩
  · intro k hk hs
    exact (ContMDiff.iff_comp_isImmersion hband).mpr ⟨hk, hs⟩

end PoincareHighDim
