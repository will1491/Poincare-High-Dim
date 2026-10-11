/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Morse.Strips.RegularBandDiffeomorph

/-!
# The induced smooth structure on a regular compact band

Flow coordinates give a smooth manifold structure on a regular band. Its compatibility with
the ambient manifold is established by smoothness of the inclusion and the smooth-lifting
criterion, rather than assumed from the product homeomorphism.
-/

namespace PoincareHighDim

open Set Topology Manifold
open scoped Manifold ContDiff

namespace SmoothTransport

variable {E H N W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace N] [TopologicalSpace W] [ChartedSpace H N]
    (I : ModelWithCorners ℝ E H) (h : N ≃ₜ W)

/-- Push forward an atlas by an explicitly specified homeomorphism. -/
@[instance_reducible]
def chartedSpace : ChartedSpace H W where
  atlas := range (fun x : N => h.symm.transOpenPartialHomeomorph (chartAt H x))
  chartAt x := h.symm.transOpenPartialHomeomorph (chartAt H (h.symm x))
  mem_chart_source x := mem_chart_source H (h.symm x)
  chart_mem_atlas _x := mem_range_self _

theorem chartAt_eq (x : W) :
    letI := chartedSpace (H := H) h
    chartAt H x = h.symm.transOpenPartialHomeomorph (chartAt H (h.symm x)) := rfl

theorem chart_transition (x y : N) :
    (h.symm.transOpenPartialHomeomorph (chartAt H x)).symm.trans
        (h.symm.transOpenPartialHomeomorph (chartAt H y)) =
      (chartAt H x).symm.trans (chartAt H y) := by
  ext z <;> simp

theorem isManifold [IsManifold I ∞ N] :
    letI := chartedSpace (H := H) h
    IsManifold I ∞ W := by
  let cs := chartedSpace (H := H) h
  refine { compatible := ?_ }
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  rw [chart_transition]
  exact StructureGroupoid.compatible (contDiffGroupoid ∞ I)
    (chart_mem_atlas H x) (chart_mem_atlas H y)

theorem contMDiff [IsManifold I ∞ N] :
    letI := chartedSpace (H := H) h
    ContMDiff I I ∞ h := by
  let cs := chartedSpace (H := H) h
  intro x
  rw [contMDiffAt_iff]
  refine ⟨h.continuous.continuousAt, ?_⟩
  have hs := (contMDiffAt_id : ContMDiffAt I I ∞ (id : N → N) x)
  rw [contMDiffAt_iff] at hs
  convert hs.2 using 1
  simp only [extChartAt, chartAt_eq, Homeomorph.transOpenPartialHomeomorph_eq_trans,
      OpenPartialHomeomorph.extend, mfld_simps, Function.comp_def,
      Homeomorph.symm_apply_apply]

theorem contMDiff_symm [IsManifold I ∞ N] :
    letI := chartedSpace (H := H) h
    ContMDiff I I ∞ h.symm := by
  let cs := chartedSpace (H := H) h
  intro x
  rw [contMDiffAt_iff]
  refine ⟨h.symm.continuous.continuousAt, ?_⟩
  have hs := (contMDiffAt_id : ContMDiffAt I I ∞ (id : N → N) (h.symm x))
  rw [contMDiffAt_iff] at hs
  convert hs.2 using 1 <;>
    simp only [extChartAt, chartAt_eq, Homeomorph.transOpenPartialHomeomorph_eq_trans,
      OpenPartialHomeomorph.extend, mfld_simps, Function.comp_def,
      Homeomorph.symm_apply_apply]

/-- A homeomorphism is a diffeomorphism for its transported atlas. Compatibility with other
smooth structures must be proved separately. -/
noncomputable def diffeomorph [IsManifold I ∞ N] :
    letI := chartedSpace (H := H) h
    N ≃ₘ⟮I, I⟯ W :=
  letI := chartedSpace (H := H) h
  { h.toEquiv with
    contMDiff_toFun := contMDiff I h
    contMDiff_invFun := contMDiff_symm I h }

end SmoothTransport

namespace RegularBand

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- Product coordinates together with smooth ambient formulas for the map and its inverse.
These formulas certify that the transported product atlas agrees with ambient smoothness. -/
structure FlowCoordinates (I : ModelWithCorners ℝ (Fin n → ℝ) H) (f : M → ℝ) (a b : ℝ) where
  flow : ℝ → M → M
  smooth_flow : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => flow p.1 p.2)
  flow_zero : ∀ x, flow 0 x = x
  homeomorph : (f ⁻¹' {a}) × Icc a b ≃ₜ (f ⁻¹' Icc a b)
  apply_eq : ∀ p, (homeomorph p).1 = flow (a - p.2.1) p.1.1
  symm_fst_eq : ∀ x, (homeomorph.symm x).1.1 = flow (f x.1 - a) x.1
  symm_snd_eq : ∀ x, (homeomorph.symm x).2.1 = f x.1

/-- A regular compact band admits product coordinates with smooth ambient flow formulas. -/
theorem nonempty_flowCoordinates {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x ∈ Icc a b → ¬ IsCriticalPt I f x) :
    Nonempty (FlowCoordinates I f a b) := by
  classical
  have hc : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
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
  let F : (f ⁻¹' {a}) × Icc a b → (f ⁻¹' Icc a b) := fun p =>
    ⟨D.flow (a - p.2.1) p.1.1, by
      have hx : f p.1.1 = a := p.1.2
      have ht := htransport p.1.1 (by rwa [hx]) p.2.1 p.2.2
      rw [hx] at ht
      change f (D.flow (a - p.2.1) p.1.1) ∈ Icc a b
      rw [ht]
      exact p.2.2⟩
  let G : (f ⁻¹' Icc a b) → (f ⁻¹' {a}) × Icc a b := fun x =>
    (⟨D.flow (f x.1 - a) x.1, htransport x.1 x.2 a hc⟩, ⟨f x.1, x.2⟩)
  have hF (p : (f ⁻¹' {a}) × Icc a b) : f (F p).1 = p.2.1 := by
    have hx : f p.1.1 = a := p.1.2
    have ht := htransport p.1.1 (by rwa [hx]) p.2.1 p.2.2
    simpa only [F, hx] using ht
  have hGF (p : (f ⁻¹' {a}) × Icc a b) : G (F p) = p := by
    apply Prod.ext
    · apply Subtype.ext
      change D.flow (f (F p).1 - a) (D.flow (a - p.2.1) p.1.1) = p.1.1
      rw [hF, D.flow_flow]
      simp only [sub_add_sub_cancel, sub_self, D.flow_zero]
    · exact Subtype.ext (hF p)
  have hFG (x : f ⁻¹' Icc a b) : F (G x) = x := by
    apply Subtype.ext
    change D.flow (a - f x.1) (D.flow (f x.1 - a) x.1) = x.1
    rw [D.flow_flow]
    simp only [sub_add_sub_cancel, sub_self, D.flow_zero]
  let Φ : (f ⁻¹' {a}) × Icc a b ≃ₜ (f ⁻¹' Icc a b) :=
    { toFun := F
      invFun := G
      left_inv := hGF
      right_inv := hFG
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact D.continuous_flow_joint.comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).prodMk
            (continuous_subtype_val.comp continuous_fst))
      continuous_invFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          exact D.continuous_flow_joint.comp
            (((hf.continuous.comp continuous_subtype_val).sub continuous_const).prodMk
              continuous_subtype_val)
        · exact (hf.continuous.comp continuous_subtype_val).subtype_mk _ }
  exact ⟨⟨D.flow, D.contMDiff_flow_joint, D.flow_zero, Φ,
    fun _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩

namespace FlowCoordinates

variable {f : M → ℝ} {a b : ℝ} [Fact (a < b)]
    {E₀ H₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [TopologicalSpace H₀] [ChartedSpace H₀ (f ⁻¹' {a})]
    (I₀ : ModelWithCorners ℝ E₀ H₀) (C : FlowCoordinates I f a b)

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- The atlas defined by regular-band flow coordinates and the given incoming-level atlas. -/
@[instance_reducible]
noncomputable def chartedSpace : ChartedSpace (ModelProd H₀ (EuclideanHalfSpace 1)) (f ⁻¹' Icc a b) :=
  SmoothTransport.chartedSpace (H := ModelProd H₀ (EuclideanHalfSpace 1)) C.homeomorph

theorem isManifold [IsManifold I₀ ∞ (f ⁻¹' {a})] :
    letI := C.chartedSpace (H₀ := H₀)
    IsManifold (I₀.prod (𝓡∂ 1)) ∞ (f ⁻¹' Icc a b) :=
  SmoothTransport.isManifold (I₀.prod (𝓡∂ 1)) C.homeomorph

/-- The flow-coordinate atlas makes the inclusion into the original ambient manifold smooth. -/
theorem contMDiff_subtypeVal [IsManifold I₀ ∞ (f ⁻¹' {a})]
    (hlevel : ContMDiff I₀ I ∞ (Subtype.val : (f ⁻¹' {a}) → M)) :
    letI := C.chartedSpace (H₀ := H₀)
    ContMDiff (I₀.prod (𝓡∂ 1)) I ∞ (Subtype.val : (f ⁻¹' Icc a b) → M) := by
  let _cs := C.chartedSpace (H₀ := H₀)
  have hF : ContMDiff (I₀.prod (𝓡∂ 1)) I ∞
      (fun p : (f ⁻¹' {a}) × Icc a b => C.flow (a - p.2.1) p.1.1) :=
    C.smooth_flow.comp
      ((contMDiff_const.sub (contMDiff_subtypeVal_Icc.comp contMDiff_snd)).prodMk
        (hlevel.comp contMDiff_fst))
  have hs := hF.comp (SmoothTransport.contMDiff_symm (I₀.prod (𝓡∂ 1)) C.homeomorph)
  apply hs.congr
  intro x
  exact (congrArg Subtype.val (C.homeomorph.apply_symm_apply x)).symm.trans
    (C.apply_eq (C.homeomorph.symm x))

/-- Smooth maps into the regular band are precisely the continuous maps whose ambient
composites are smooth. This verifies that the transported atlas is the induced smooth atlas. -/
theorem contMDiff_iff [IsManifold I₀ ∞ (f ⁻¹' {a})]
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    [TopologicalSpace HN] [TopologicalSpace N] [ChartedSpace HN N]
    (J : ModelWithCorners ℝ EN HN) [IsManifold J ∞ N]
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hlevel : ContMDiff I₀ I ∞ (Subtype.val : (f ⁻¹' {a}) → M))
    (hliftlevel : ∀ k : N → (f ⁻¹' {a}), Continuous k →
      ContMDiff J I ∞ (fun x => (k x).1) → ContMDiff J I₀ ∞ k)
    {k : N → (f ⁻¹' Icc a b)} :
    letI := C.chartedSpace (H₀ := H₀)
    ContMDiff J (I₀.prod (𝓡∂ 1)) ∞ k ↔
      Continuous k ∧ ContMDiff J I ∞ (fun x => (k x).1) := by
  let _cs := C.chartedSpace (H₀ := H₀)
  constructor
  · intro hk
    exact ⟨hk.continuous, (C.contMDiff_subtypeVal I₀ hlevel).comp hk⟩
  · rintro ⟨hkcont, hk⟩
    have hG : ContMDiff J (I₀.prod (𝓡∂ 1)) ∞ (fun x => C.homeomorph.symm (k x)) := by
      apply ContMDiff.prodMk
      · apply hliftlevel
        · exact continuous_fst.comp (C.homeomorph.symm.continuous.comp hkcont)
        · have hs := C.smooth_flow.comp (((hf.comp hk).sub (contMDiff_const (c := a))).prodMk hk)
          exact hs.congr (fun x => C.symm_fst_eq (k x))
      · rw [contMDiff_iff_comp_subtypeVal_Icc]
        refine ⟨continuous_snd.comp (C.homeomorph.symm.continuous.comp hkcont), ?_⟩
        exact (hf.comp hk).congr (fun x => C.symm_snd_eq (k x))
    have hs := (SmoothTransport.contMDiff (I₀.prod (𝓡∂ 1)) C.homeomorph).comp hG
    exact hs.congr (fun x => (C.homeomorph.apply_symm_apply (k x)).symm)

/-- The band flow is a diffeomorphism for the induced atlas, whose compatibility with ambient
smoothness is proved by `contMDiff_subtypeVal` and `contMDiff_iff`. -/
noncomputable def diffeomorph [IsManifold I₀ ∞ (f ⁻¹' {a})] :
    letI := C.chartedSpace (H₀ := H₀)
    ((f ⁻¹' {a}) × Icc a b) ≃ₘ⟮I₀.prod (𝓡∂ 1), I₀.prod (𝓡∂ 1)⟯ (f ⁻¹' Icc a b) :=
  SmoothTransport.diffeomorph (I₀.prod (𝓡∂ 1)) C.homeomorph

omit [Fact (a < b)]

/-- Product height is the original defining function. -/
theorem value_homeomorph (p : (f ⁻¹' {a}) × Icc a b) :
    f (C.homeomorph p).1 = p.2.1 := by
  have h := C.symm_snd_eq (C.homeomorph p)
  simpa only [Homeomorph.symm_apply_apply] using h.symm

/-- The flow-coordinate product map fixes the incoming level pointwise. -/
theorem incoming_homeomorph (v : f ⁻¹' {a}) (ha : a ∈ Icc a b) :
    (C.homeomorph (v, ⟨a, ha⟩)).1 = v.1 := by
  rw [C.apply_eq]
  exact (congrArg (fun t => C.flow t v.1) (sub_self a)).trans (C.flow_zero v.1)

end FlowCoordinates
end RegularBand
end PoincareHighDim
