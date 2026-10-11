/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.BoundarySign
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Patching signed boundary coordinates into a strip function

A finite cover describes a compact domain by local smooth functions taking values in
`[0,1]` inside, with its two boundary pieces at the endpoints. Outside the domain,
overlapping descriptions must select the same side of the interval. Normalizing a
subordinate partition of unity gives a defining function on an open neighborhood.
-/

namespace PoincareHighDim
namespace StripFunction

open Set Topology Filter
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)
    {S B₀ B₁ : Set M}

/-- Finite local signed descriptions of a domain and its two boundary components.
The last condition states that overlapping descriptions agree on the exterior side. -/
structure SignedCover (S B₀ B₁ : Set M) where
  size : ℕ
  domain : Fin size → Set M
  open_domain : ∀ i, IsOpen (domain i)
  covers : S ⊆ ⋃ i, domain i
  value : Fin size → M → ℝ
  smooth : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (value i) (domain i)
  lower_subset : B₀ ⊆ S
  upper_subset : B₁ ⊆ S
  inside : ∀ i x, x ∈ domain i → x ∈ S → value i x ∈ Icc (0 : ℝ) 1
  lower : ∀ i x, x ∈ domain i → x ∈ S → (value i x = 0 ↔ x ∈ B₀)
  upper : ∀ i x, x ∈ domain i → x ∈ S → (value i x = 1 ↔ x ∈ B₁)
  outside : ∀ i x, x ∈ domain i → x ∉ S → value i x < 0 ∨ 1 < value i x
  compatible : ∀ i j x, x ∈ domain i → x ∈ domain j → x ∉ S →
    (value i x < 0 ↔ value j x < 0)

namespace SignedCover

variable {I} (C : SignedCover I S B₀ B₁)

/-- A subordinate smooth partition exists on the compact domain. -/
theorem exists_partition [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (hS : IsClosed S) :
    ∃ ρ : SmoothPartitionOfUnity (Fin C.size) I M S, ρ.IsSubordinate C.domain :=
  SmoothPartitionOfUnity.exists_isSubordinate I hS C.domain C.open_domain C.covers

variable (ρ : SmoothPartitionOfUnity (Fin C.size) I M S)
    (hρ : ρ.IsSubordinate C.domain)

/-- Total weight, positive on an open neighborhood of the domain. -/
noncomputable def weight (x : M) : ℝ := ∑ i, ρ i x

/-- The unnormalized weighted function. -/
noncomputable def numerator (x : M) : ℝ := ∑ i, ρ i x * C.value i x

/-- Normalized weighted local defining functions. -/
noncomputable def function (x : M) : ℝ := C.numerator ρ x / C.weight ρ x

/-- The neighborhood on which the normalization is well defined. -/
def neighborhood : Set M := {x | 0 < C.weight ρ x}

theorem smooth_weight : ContMDiff I 𝓘(ℝ, ℝ) ∞ (C.weight ρ) :=
  ContMDiff.sum fun i _ => (ρ i).contMDiff

theorem weight_eq_one {x : M} (hx : x ∈ S) : C.weight ρ x = 1 := by
  simpa only [weight, finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx

theorem open_neighborhood : IsOpen (C.neighborhood ρ) :=
  isOpen_lt continuous_const (C.smooth_weight ρ).continuous

theorem subset_neighborhood : S ⊆ C.neighborhood ρ := by
  intro x hx
  change 0 < C.weight ρ x
  rw [C.weight_eq_one ρ hx]
  exact zero_lt_one

include hρ

theorem smooth_summand (i : Fin C.size) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => ρ i x * C.value i x) := by
  have h := ρ.contMDiff_smul (g := C.value i) (n := ⊤)
    (fun x hx => (C.smooth i).contMDiffAt ((C.open_domain i).mem_nhds (hρ i hx)))
  simpa only [smul_eq_mul] using h

theorem smooth_numerator : ContMDiff I 𝓘(ℝ, ℝ) ∞ (C.numerator ρ) :=
  ContMDiff.sum fun i _ => C.smooth_summand ρ hρ i

theorem smooth_function : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (C.function ρ) (C.neighborhood ρ) :=
  (C.smooth_numerator ρ hρ).contMDiffOn.div₀ (C.smooth_weight ρ).contMDiffOn
    (fun _ hx => ne_of_gt hx)

theorem active_source {i : Fin C.size} {x : M} (hi : ρ i x ≠ 0) : x ∈ C.domain i :=
  hρ i (subset_tsupport _ hi)

theorem summand_nonneg {x : M} (hx : x ∈ S) (i : Fin C.size) :
    0 ≤ ρ i x * C.value i x := by
  by_cases hi : ρ i x = 0
  · simp [hi]
  · exact mul_nonneg (ρ.nonneg i x) (C.inside i x (C.active_source ρ hρ hi) hx).1

theorem summand_le_weight {x : M} (hx : x ∈ S) (i : Fin C.size) :
    ρ i x * C.value i x ≤ ρ i x := by
  by_cases hi : ρ i x = 0
  · simp [hi]
  · exact mul_le_of_le_one_right (ρ.nonneg i x)
      (C.inside i x (C.active_source ρ hρ hi) hx).2

theorem value_mem_Icc {x : M} (hx : x ∈ S) : C.function ρ x ∈ Icc (0 : ℝ) 1 := by
  rw [function, C.weight_eq_one ρ hx, div_one]
  refine ⟨Finset.sum_nonneg (fun i _ => C.summand_nonneg ρ hρ hx i), ?_⟩
  calc C.numerator ρ x ≤ C.weight ρ x :=
      Finset.sum_le_sum fun i _ => C.summand_le_weight ρ hρ hx i
    _ = 1 := C.weight_eq_one ρ hx

theorem numerator_eq_zero {x : M} (hx : x ∈ B₀) : C.numerator ρ x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : ρ i x = 0
  · simp [hi]
  · rw [(C.lower i x (C.active_source ρ hρ hi) (C.lower_subset hx)).mpr hx, mul_zero]

theorem numerator_eq_weight {x : M} (hx : x ∈ B₁) : C.numerator ρ x = C.weight ρ x := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : ρ i x = 0
  · simp [hi]
  · rw [(C.upper i x (C.active_source ρ hρ hi) (C.upper_subset hx)).mpr hx, mul_one]

theorem value_pos {x : M} (hx : x ∈ S) (hb : x ∉ B₀) : 0 < C.function ρ x := by
  obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem hx
  have hs := C.active_source ρ hρ (ne_of_gt hi)
  have hg : 0 < C.value i x := lt_of_le_of_ne (C.inside i x hs hx).1
    (Ne.symm (mt (C.lower i x hs hx).mp hb))
  rw [function, C.weight_eq_one ρ hx, div_one]
  exact (mul_pos hi hg).trans_le (Finset.single_le_sum
    (fun j _ => C.summand_nonneg ρ hρ hx j) (Finset.mem_univ i))

theorem value_lt_one {x : M} (hx : x ∈ S) (hb : x ∉ B₁) : C.function ρ x < 1 := by
  obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem hx
  have hs := C.active_source ρ hρ (ne_of_gt hi)
  have hg : C.value i x < 1 := lt_of_le_of_ne (C.inside i x hs hx).2
    (mt (C.upper i x hs hx).mp hb)
  rw [function, C.weight_eq_one ρ hx, div_one, ← C.weight_eq_one ρ hx]
  exact Finset.sum_lt_sum (fun j _ => C.summand_le_weight ρ hρ hx j)
    ⟨i, Finset.mem_univ i, (mul_lt_mul_of_pos_left hg hi).trans_eq (mul_one _)⟩

/-- Outside the domain, normalization remains strictly on one exterior side. -/
theorem value_outside {x : M} (hx : x ∈ C.neighborhood ρ) (hS : x ∉ S) :
    C.function ρ x < 0 ∨ 1 < C.function ρ x := by
  classical
  have hp : 0 < ∑ i, ρ i x := hx
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => ρ.nonneg j x)).mp hp
  have hsi := C.active_source ρ hρ (ne_of_gt hi)
  rcases C.outside i x hsi hS with hneg | hpos
  · left
    have hle : ∀ j, ρ j x * C.value j x ≤ 0 := by
      intro j
      by_cases hj : ρ j x = 0
      · simp [hj]
      · exact mul_nonpos_of_nonneg_of_nonpos (ρ.nonneg j x)
          ((C.compatible i j x hsi (C.active_source ρ hρ hj) hS).mp hneg).le
    have hnum : C.numerator ρ x < 0 := by
      have hh := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) => hle j)
        ⟨i, Finset.mem_univ i, mul_neg_of_pos_of_neg hi hneg⟩
      simpa only [numerator, Finset.sum_const_zero] using hh
    exact div_neg_of_neg_of_pos hnum hx
  · right
    have hle : ∀ j, ρ j x ≤ ρ j x * C.value j x := by
      intro j
      by_cases hj : ρ j x = 0
      · simp [hj]
      · have hsj := C.active_source ρ hρ hj
        have hjpos : 1 < C.value j x := by
          rcases C.outside j x hsj hS with hn | hp
          · have := (C.compatible j i x hsj hsi hS).mp hn
            linarith
          · exact hp
        exact le_mul_of_one_le_right (ρ.nonneg j x) hjpos.le
    have hnum : C.weight ρ x < C.numerator ρ x :=
      Finset.sum_lt_sum (fun j _ => hle j)
        ⟨i, Finset.mem_univ i, by simpa only [mul_one] using mul_lt_mul_of_pos_left hpos hi⟩
    exact (lt_div_iff₀ hx).mpr (by simpa only [one_mul] using hnum)

theorem mem_strip_iff {x : M} (hx : x ∈ C.neighborhood ρ) :
    C.function ρ x ∈ Icc (0 : ℝ) 1 ↔ x ∈ S := by
  constructor
  · intro h
    by_contra hn
    rcases C.value_outside ρ hρ hx hn with hl | hu
    · exact (not_lt_of_ge h.1) hl
    · exact (not_lt_of_ge h.2) hu
  · exact C.value_mem_Icc ρ hρ

theorem lower_level_iff {x : M} (hx : x ∈ C.neighborhood ρ) :
    C.function ρ x = 0 ↔ x ∈ B₀ := by
  constructor
  · intro h
    have hS := (C.mem_strip_iff ρ hρ hx).mp (by simp [h])
    by_contra hn
    exact (ne_of_gt (C.value_pos ρ hρ hS hn)) h
  · intro h
    rw [function, C.numerator_eq_zero ρ hρ h, zero_div]

theorem upper_level_iff {x : M} (hx : x ∈ C.neighborhood ρ) :
    C.function ρ x = 1 ↔ x ∈ B₁ := by
  constructor
  · intro h
    have hS := (C.mem_strip_iff ρ hρ hx).mp (by simp [h])
    by_contra hn
    exact (ne_of_lt (C.value_lt_one ρ hρ hS hn)) h
  · intro h
    rw [function, C.numerator_eq_weight ρ hρ h, div_self (ne_of_gt hx)]

omit hρ in
include C in
/-- The patched function realizes the domain as a closed strip in an open neighborhood,
with exactly the prescribed endpoint level sets. -/
theorem exists_strip_function [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (hS : IsClosed S) :
    ∃ (O : Set M) (f : M → ℝ), IsOpen O ∧ S ⊆ O ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f O ∧
      (∀ x ∈ O, f x ∈ Icc (0 : ℝ) 1 ↔ x ∈ S) ∧
      (∀ x ∈ O, f x = 0 ↔ x ∈ B₀) ∧
      (∀ x ∈ O, f x = 1 ↔ x ∈ B₁) := by
  obtain ⟨ρ, hρ⟩ := C.exists_partition hS
  exact ⟨C.neighborhood ρ, C.function ρ, C.open_neighborhood ρ,
    C.subset_neighborhood ρ, C.smooth_function ρ hρ,
    fun _ hx => C.mem_strip_iff ρ hρ hx, fun _ hx => C.lower_level_iff ρ hρ hx,
    fun _ hx => C.upper_level_iff ρ hρ hx⟩

/-- An inward test curve supplied by a local signed boundary chart. It enters the domain
on the positive half-ray and increases that chart's defining function to first order. -/
def HasLowerCurves : Prop :=
  ∀ x ∈ B₀, ∀ i, x ∈ C.domain i →
    ∃ (γ : ℝ → M) (d : ℝ), ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ 0 ∧ γ 0 = x ∧
      (∀ᶠ t in 𝓝[≥] (0 : ℝ), γ t ∈ S) ∧
      HasDerivAt (C.value i ∘ γ) d 0 ∧ 0 < d

set_option backward.isDefEq.respectTransparency false in
/-- Normalization preserves regularity at the lower boundary. Compatibility of different
normal derivatives follows from their nonnegativity along the same inward half-curve. -/
theorem regular_lower [IsManifold I ∞ M] (hcurves : C.HasLowerCurves) {x : M} (hx : x ∈ B₀) :
    mfderiv I 𝓘(ℝ, ℝ) (C.function ρ) x ≠ 0 := by
  classical
  have hxS := C.lower_subset hx
  obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem hxS
  have his := C.active_source ρ hρ (ne_of_gt hi)
  obtain ⟨γ, d, hγ, hγ0, hγS, hd, hdpos⟩ := hcurves x hx i his
  let a (j : Fin C.size) (t : ℝ) := ρ j (γ t) * C.value j (γ t)
  have ha (j : Fin C.size) : DifferentiableAt ℝ (a j) 0 := by
    apply mdifferentiableAt_iff_differentiableAt.mp
    exact ((C.smooth_summand ρ hρ j).contMDiffAt.comp 0 hγ).mdifferentiableAt (by simp)
  have ha0 (j : Fin C.size) : a j 0 = 0 := by
    change ρ j (γ 0) * C.value j (γ 0) = 0
    rw [hγ0]
    by_cases hj : ρ j x = 0
    · simp [hj]
    · rw [(C.lower j x (C.active_source ρ hρ hj) hxS).mpr hx, mul_zero]
  have hnonneg (j : Fin C.size) : 0 ≤ deriv (a j) 0 := by
    have hmin : IsLocalMinOn (a j) (Ici 0) 0 := by
      filter_upwards [hγS] with t ht
      change a j 0 ≤ a j t
      rw [ha0]
      exact C.summand_nonneg ρ hρ ht j
    have hv : (1 : ℝ) ∈ posTangentConeAt (Ici 0) 0 := by
      simpa only [sub_zero] using sub_mem_posTangentConeAt_of_segment_subset
        ((convex_Ici (0 : ℝ)).segment_subset (show (0 : ℝ) ∈ Ici 0 by simp)
          (show (1 : ℝ) ∈ Ici 0 by norm_num))
    simpa using hmin.hasFDerivWithinAt_nonneg
      (ha j).hasDerivAt.hasFDerivAt.hasFDerivWithinAt hv
  have hρdiff : DifferentiableAt ℝ (fun t => ρ i (γ t)) 0 := by
    apply mdifferentiableAt_iff_differentiableAt.mp
    exact ((ρ i).contMDiff.contMDiffAt.comp 0 hγ).mdifferentiableAt (by simp)
  have hactive : 0 < deriv (a i) 0 := by
    have hprod := (hρdiff.hasDerivAt.mul hd).deriv
    change deriv (a i) 0 = _ at hprod
    rw [Function.comp_apply, hγ0, (C.lower i x his hxS).mpr hx, mul_zero, zero_add] at hprod
    rw [hprod]
    exact mul_pos hi hdpos
  have hsumpos : 0 < ∑ j, deriv (a j) 0 :=
    hactive.trans_le (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i))
  have hnum : HasDerivAt (C.numerator ρ ∘ γ) (∑ j, deriv (a j) 0) 0 := by
    change HasDerivAt (fun t => ∑ j, a j t) _ 0
    convert (HasDerivAt.sum (u := Finset.univ) fun j _ => (ha j).hasDerivAt) using 1
    ext t
    simp
  have hw : DifferentiableAt ℝ (C.weight ρ ∘ γ) 0 := by
    apply mdifferentiableAt_iff_differentiableAt.mp
    exact ((C.smooth_weight ρ).contMDiffAt.comp 0 hγ).mdifferentiableAt (by simp)
  have hw0 : (C.weight ρ ∘ γ) 0 = 1 := by
    rw [Function.comp_apply, hγ0, C.weight_eq_one ρ hxS]
  have hn0 : (C.numerator ρ ∘ γ) 0 = 0 := by
    rw [Function.comp_apply, hγ0, C.numerator_eq_zero ρ hρ hx]
  have hfderiv : HasDerivAt (C.function ρ ∘ γ) (∑ j, deriv (a j) 0) 0 := by
    have h := hnum.div hw.hasDerivAt (by rw [hw0]; norm_num)
    convert h using 1
    · rfl
    · simp only [hn0, hw0, mul_one, zero_mul, sub_zero, one_pow, div_one]
  have hfx := (C.smooth_function ρ hρ).contMDiffAt
    ((C.open_neighborhood ρ).mem_nhds (C.subset_neighborhood ρ hxS))
  intro hz
  have hzero : (mfderiv I 𝓘(ℝ, ℝ) (C.function ρ) (γ 0) : E →L[ℝ] ℝ) = 0 :=
    hγ0.symm ▸ hz
  have hchain := mfderiv_comp 0 (hγ0.symm ▸ hfx.mdifferentiableAt (by simp))
    (hγ.mdifferentiableAt (by simp))
  have hchain' := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hchain
  have hleft : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (C.function ρ ∘ γ) 0) (1 : ℝ) =
      ∑ j, deriv (a j) 0 := by
    rw [mfderiv_eq_fderiv, hfderiv.hasFDerivAt.fderiv]
    change (1 : ℝ) * (∑ j, deriv (a j) 0) = _
    exact one_mul _
  have hsumzero : (∑ j, deriv (a j) 0) = 0 := by
    calc
      (∑ j, deriv (a j) 0) = (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (C.function ρ ∘ γ) 0) (1 : ℝ) := hleft.symm
      _ = (mfderiv I 𝓘(ℝ, ℝ) (C.function ρ) (γ 0))
          ((mfderiv 𝓘(ℝ, ℝ) I γ 0) (1 : ℝ)) := hchain'
      _ = 0 := congrArg (fun L : E →L[ℝ] ℝ =>
        L ((mfderiv 𝓘(ℝ, ℝ) I γ 0) (1 : ℝ))) hzero
  exact hsumpos.ne' hsumzero

/-- Reverse the two ends by reflecting local functions across the midpoint. -/
noncomputable def reverse : SignedCover I S B₁ B₀ where
  size := C.size
  domain := C.domain
  open_domain := C.open_domain
  covers := C.covers
  value i x := 1 - C.value i x
  smooth i := contMDiffOn_const.sub (C.smooth i)
  lower_subset := C.upper_subset
  upper_subset := C.lower_subset
  inside i x hu hx := by
    have h := C.inside i x hu hx
    constructor <;> linarith [h.1, h.2]
  lower i x hu hx := by
    rw [← C.upper i x hu hx]
    constructor <;> intro h <;> linarith
  upper i x hu hx := by
    rw [← C.lower i x hu hx]
    constructor <;> intro h <;> linarith
  outside i x hu hx := by
    rcases C.outside i x hu hx with h | h
    · right; linarith
    · left; linarith
  compatible i j x hi hj hx := by
    have hc := C.compatible i j x hi hj hx
    have hoi := C.outside i x hi hx
    have hoj := C.outside j x hj hx
    constructor <;> intro h
    · rcases hoj with hj | hj
      · have := hc.mpr hj; linarith
      · linarith
    · rcases hoi with hi | hi
      · have := hc.mp hi; linarith
      · linarith

omit hρ in
theorem reverse_function {x : M} (hx : x ∈ C.neighborhood ρ) :
    C.reverse.function ρ x = 1 - C.function ρ x := by
  have hn : C.reverse.numerator ρ x = C.weight ρ x - C.numerator ρ x := by
    simp only [numerator, reverse, weight, mul_sub, mul_one, Finset.sum_sub_distrib]
    rfl
  change C.reverse.numerator ρ x / C.weight ρ x = _
  rw [hn, sub_div, div_self (ne_of_gt hx)]
  rfl

/-- Upper-end regularity is lower-end regularity for the reflected local functions. -/
theorem regular_upper [IsManifold I ∞ M] (hcurves : C.reverse.HasLowerCurves) {x : M} (hx : x ∈ B₁) :
    mfderiv I 𝓘(ℝ, ℝ) (C.function ρ) x ≠ 0 := by
  have hne := C.reverse.regular_lower ρ hρ hcurves hx
  have hxO := C.subset_neighborhood ρ (C.upper_subset hx)
  have heq : C.reverse.function ρ =ᶠ[𝓝 x] (fun y => 1 - C.function ρ y) := by
    filter_upwards [(C.open_neighborhood ρ).mem_nhds hxO] with y hy
    exact C.reverse_function ρ hy
  have hdiff := ((C.smooth_function ρ hρ).contMDiffAt
    ((C.open_neighborhood ρ).mem_nhds hxO)).mdifferentiableAt (by simp)
  intro hz
  have hh := ((hasMFDerivAt_const (I := I) (1 : ℝ) x).sub hdiff.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  have hval := hh.mfderiv
  apply hne
  apply hval.trans
  ext v
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hz
  let z : ℝ := (mfderiv I 𝓘(ℝ, ℝ) (C.function ρ) x) v
  change (0 : ℝ) - z = 0
  change z = 0 at hv
  rw [hv, sub_self]

omit hρ in
include C in
/-- Genuine local signed charts, with their inward curves, produce a global regular strip
function on an open neighborhood of the compact domain. -/
theorem exists_regular_strip_function [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] (hS : IsClosed S)
    (hlower : C.HasLowerCurves) (hupper : C.reverse.HasLowerCurves) :
    ∃ (O : Set M) (f : M → ℝ), IsOpen O ∧ S ⊆ O ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f O ∧
      (∀ x ∈ O, f x ∈ Icc (0 : ℝ) 1 ↔ x ∈ S) ∧
      (∀ x ∈ O, f x = 0 ↔ x ∈ B₀) ∧
      (∀ x ∈ O, f x = 1 ↔ x ∈ B₁) ∧
      (∀ x ∈ B₀ ∪ B₁, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) := by
  obtain ⟨ρ, hρ⟩ := C.exists_partition hS
  refine ⟨C.neighborhood ρ, C.function ρ, C.open_neighborhood ρ,
    C.subset_neighborhood ρ, C.smooth_function ρ hρ,
    fun _ hx => C.mem_strip_iff ρ hρ hx, fun _ hx => C.lower_level_iff ρ hρ hx,
    fun _ hx => C.upper_level_iff ρ hρ hx, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · exact C.regular_lower ρ hρ hlower hx
  · exact C.regular_upper ρ hρ hupper hx

end SignedCover
end StripFunction
end PoincareHighDim
