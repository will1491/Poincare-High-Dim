/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.StripFunction

/-!
# Finite signed covers from local boundary descriptions

The two compact boundary pieces admit disjoint ambient neighborhoods. Local signed
coordinates are restricted to these neighborhoods and to values between `-1/4` and
`1/4`; the remaining interior uses the constant `1/2`. Compactness then selects a
finite cover to which the regular strip-function construction applies.
-/

namespace PoincareHighDim
namespace StripFunction

open Set Topology Filter
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)

/-- A smooth signed coordinate for one boundary component, together with its inward
coordinate curves. These data are local; no collar or global defining function is assumed. -/
structure LocalBoundaryFunction (S B : Set M) (b : M) where
  domain : Set M
  open_domain : IsOpen domain
  mem_domain : b ∈ domain
  value : M → ℝ
  smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ value domain
  side : ∀ x ∈ domain, x ∈ S ↔ 0 ≤ value x
  zero : ∀ x ∈ domain, x ∈ B ↔ value x = 0
  inward : ∀ x ∈ domain, x ∈ B →
    ∃ (γ : ℝ → M) (d : ℝ), ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ 0 ∧ γ 0 = x ∧
      (∀ᶠ t in 𝓝[≥] (0 : ℝ), γ t ∈ S) ∧
      HasDerivAt (value ∘ γ) d 0 ∧ 0 < d

/-- One patch in a signed cover, recording which of two disjoint exterior neighborhoods
contains each exterior point. -/
structure RegularPatch (S B₀ B₁ N₀ N₁ : Set M) where
  domain : Set M
  open_domain : IsOpen domain
  value : M → ℝ
  smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ value domain
  inside : ∀ x ∈ domain, x ∈ S → value x ∈ Icc (0 : ℝ) 1
  lower : ∀ x ∈ domain, x ∈ S → (value x = 0 ↔ x ∈ B₀)
  upper : ∀ x ∈ domain, x ∈ S → (value x = 1 ↔ x ∈ B₁)
  outside : ∀ x ∈ domain, x ∉ S →
    (value x < 0 ∧ x ∈ N₀) ∨ (1 < value x ∧ x ∈ N₁)
  lower_curves : ∀ x ∈ domain, x ∈ B₀ →
    ∃ (γ : ℝ → M) (d : ℝ), ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ 0 ∧ γ 0 = x ∧
      (∀ᶠ t in 𝓝[≥] (0 : ℝ), γ t ∈ S) ∧
      HasDerivAt (value ∘ γ) d 0 ∧ 0 < d
  upper_curves : ∀ x ∈ domain, x ∈ B₁ →
    ∃ (γ : ℝ → M) (d : ℝ), ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ 0 ∧ γ 0 = x ∧
      (∀ᶠ t in 𝓝[≥] (0 : ℝ), γ t ∈ S) ∧
      HasDerivAt ((fun y => 1 - value y) ∘ γ) d 0 ∧ 0 < d

namespace RegularPatch

variable {I} {S B₀ B₁ N₀ N₁ : Set M}

/-- Reflection exchanges the two boundary labels and their exterior neighborhoods. -/
noncomputable def reverse (P : RegularPatch I S B₀ B₁ N₀ N₁) :
    RegularPatch I S B₁ B₀ N₁ N₀ where
  domain := P.domain
  open_domain := P.open_domain
  value x := 1 - P.value x
  smooth := contMDiffOn_const.sub P.smooth
  inside x hu hx := by
    have h := P.inside x hu hx
    constructor <;> linarith [h.1, h.2]
  lower x hu hx := by
    rw [← P.upper x hu hx]
    constructor <;> intro h <;> linarith
  upper x hu hx := by
    rw [← P.lower x hu hx]
    constructor <;> intro h <;> linarith
  outside x hu hx := by
    rcases P.outside x hu hx with h | h
    · exact Or.inr ⟨by linarith [h.1], h.2⟩
    · exact Or.inl ⟨by linarith [h.1], h.2⟩
  lower_curves := P.upper_curves
  upper_curves x hu hx := by
    obtain ⟨γ, d, hγ, hγ0, hγS, hd, hp⟩ := P.lower_curves x hu hx
    refine ⟨γ, d, hγ, hγ0, hγS, ?_, hp⟩
    convert hd using 1
    ext t
    simp

/-- A boundary chart becomes a lower-end patch after shrinking into the appropriate
exterior neighborhood and keeping the signed coordinate smaller than `1/4`. -/
noncomputable def of_lower {b : M} (L : LocalBoundaryFunction I S B₀ b)
    (hN₀ : IsOpen N₀) (hB₁ : B₁ ⊆ N₁) (hdisj : Disjoint N₀ N₁) :
    RegularPatch I S B₀ B₁ N₀ N₁ where
  domain := (L.domain ∩ L.value ⁻¹' Ioo (-(1 / 4 : ℝ)) (1 / 4)) ∩ N₀
  open_domain := (L.smooth.continuousOn.isOpen_inter_preimage L.open_domain isOpen_Ioo).inter hN₀
  value := L.value
  smooth := L.smooth.mono (inter_subset_left.trans inter_subset_left)
  inside x hu hx := ⟨(L.side x hu.1.1).mp hx, le_of_lt (lt_trans hu.1.2.2 (by norm_num))⟩
  lower x hu _ := (L.zero x hu.1.1).symm
  upper x hu _ := by
    constructor
    · intro h
      linarith [hu.1.2.2]
    · intro h
      exact False.elim (Set.disjoint_left.mp hdisj hu.2 (hB₁ h))
  outside x hu hx := Or.inl ⟨lt_of_not_ge (mt (L.side x hu.1.1).mpr hx), hu.2⟩
  lower_curves x hu hx := L.inward x hu.1.1 hx
  upper_curves x hu hx := False.elim (Set.disjoint_left.mp hdisj hu.2 (hB₁ hx))

theorem mem_of_lower {b : M} (L : LocalBoundaryFunction I S B₀ b)
    (hb : b ∈ B₀) (hN₀ : IsOpen N₀) (hB₁ : B₁ ⊆ N₁) (hdisj : Disjoint N₀ N₁)
    (hbN : b ∈ N₀) : b ∈ (of_lower L hN₀ hB₁ hdisj).domain := by
  refine ⟨⟨L.mem_domain, ?_⟩, hbN⟩
  change L.value b ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4)
  rw [(L.zero b L.mem_domain).mp hb]
  norm_num

/-- The interior is covered by a constant patch away from both endpoint values. -/
noncomputable def interiorPatch
    (hboundary : B₀ ∪ B₁ ⊆ frontier S) : RegularPatch I S B₀ B₁ N₀ N₁ where
  domain := interior S
  open_domain := isOpen_interior
  value _ := 1 / 2
  smooth := contMDiffOn_const
  inside _ _ _ := by norm_num
  lower x hu _ := by
    constructor
    · norm_num
    · intro h
      exact False.elim ((hboundary (Or.inl h)).2 hu)
  upper x hu _ := by
    constructor
    · norm_num
    · intro h
      exact False.elim ((hboundary (Or.inr h)).2 hu)
  outside x hu hx := False.elim (hx (interior_subset hu))
  lower_curves x hu hx := False.elim ((hboundary (Or.inl hx)).2 hu)
  upper_curves x hu hx := False.elim ((hboundary (Or.inr hx)).2 hu)

end RegularPatch

/-- A compact domain covered by regular signed patches has a finite signed cover with
both families of inward curves. -/
theorem exists_finite_signedCover {S B₀ B₁ N₀ N₁ : Set M}
    (hS : IsCompact S) (hB₀ : B₀ ⊆ S) (hB₁ : B₁ ⊆ S) (hdisj : Disjoint N₀ N₁)
    (hpatch : ∀ x ∈ S, ∃ P : RegularPatch I S B₀ B₁ N₀ N₁, x ∈ P.domain) :
    ∃ C : SignedCover I S B₀ B₁, C.HasLowerCurves ∧ C.reverse.HasLowerCurves := by
  classical
  let P : S → RegularPatch I S B₀ B₁ N₀ N₁ := fun x => (hpatch x x.2).choose
  have hP (x : S) : x.1 ∈ (P x).domain := (hpatch x x.2).choose_spec
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover (fun x : S => (P x).domain)
    (fun x => (P x).open_domain) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hP ⟨x, hx⟩⟩)
  let Q (i : Fin s.card) := P (s.equivFin.symm i).1
  have hcover : S ⊆ ⋃ i, (Q i).domain := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    refine mem_iUnion.mpr ⟨s.equivFin ⟨y, hy⟩, ?_⟩
    simpa only [Q, Equiv.symm_apply_apply] using hxy
  let C : SignedCover I S B₀ B₁ := {
    size := s.card
    domain := fun i => (Q i).domain
    open_domain := fun i => (Q i).open_domain
    covers := hcover
    value := fun i => (Q i).value
    smooth := fun i => (Q i).smooth
    lower_subset := hB₀
    upper_subset := hB₁
    inside := fun i => (Q i).inside
    lower := fun i => (Q i).lower
    upper := fun i => (Q i).upper
    outside := fun i x hu hx => ((Q i).outside x hu hx).imp And.left And.left
    compatible := fun i j x hi hj hx => by
      have hsi := (Q i).outside x hi hx
      have hsj := (Q j).outside x hj hx
      constructor <;> intro h
      · rcases hsj with hsj | hsj
        · exact hsj.1
        · rcases hsi with hsi | hsi
          · exact False.elim (Set.disjoint_left.mp hdisj hsi.2 hsj.2)
          · linarith [hsi.1]
      · rcases hsi with hsi | hsi
        · exact hsi.1
        · rcases hsj with hsj | hsj
          · exact False.elim (Set.disjoint_left.mp hdisj hsj.2 hsi.2)
          · linarith [hsj.1] }
  exact ⟨C, fun x hx i hu => (Q i).lower_curves x hu hx,
    fun x hx i hu => (Q i).upper_curves x hu hx⟩

/-- Local signed descriptions of the two compact boundary pieces produce the finite
regular cover used in the partition construction. -/
theorem exists_signedCover_of_local_boundary [T2Space M] {S B₀ B₁ : Set M}
    (hS : IsCompact S) (hB₀ : IsCompact B₀) (hB₁ : IsCompact B₁)
    (hB₀S : B₀ ⊆ S) (hB₁S : B₁ ⊆ S) (hdisj : Disjoint B₀ B₁)
    (hfrontier : frontier S = B₀ ∪ B₁)
    (hlocal₀ : ∀ b ∈ B₀, Nonempty (LocalBoundaryFunction I S B₀ b))
    (hlocal₁ : ∀ b ∈ B₁, Nonempty (LocalBoundaryFunction I S B₁ b)) :
    ∃ C : SignedCover I S B₀ B₁, C.HasLowerCurves ∧ C.reverse.HasLowerCurves := by
  obtain ⟨N₀, N₁, hN₀, hN₁, hB₀N, hB₁N, hNdisj⟩ :=
    SeparatedNhds.of_isCompact_isCompact hB₀ hB₁ hdisj
  apply exists_finite_signedCover I hS hB₀S hB₁S hNdisj
  intro x hx
  by_cases hx₀ : x ∈ B₀
  · obtain ⟨L⟩ := hlocal₀ x hx₀
    exact ⟨RegularPatch.of_lower L hN₀ hB₁N hNdisj,
      RegularPatch.mem_of_lower L hx₀ hN₀ hB₁N hNdisj (hB₀N hx₀)⟩
  by_cases hx₁ : x ∈ B₁
  · obtain ⟨L⟩ := hlocal₁ x hx₁
    exact ⟨(RegularPatch.of_lower L hN₁ hB₀N hNdisj.symm).reverse,
      RegularPatch.mem_of_lower L hx₁ hN₁ hB₀N hNdisj.symm (hB₁N hx₁)⟩
  · refine ⟨RegularPatch.interiorPatch (N₀ := N₀) (N₁ := N₁) hfrontier.ge, ?_⟩
    change x ∈ interior S
    by_contra hn
    have hf : x ∈ frontier S := ⟨subset_closure hx, hn⟩
    rw [hfrontier] at hf
    exact hf.elim hx₀ hx₁

/-- Local signed boundary coordinates suffice for a globally smooth regular strip function
on an open neighborhood of the compact embedded domain. -/
theorem exists_regular_strip_function_of_local_boundary [IsManifold I ∞ M]
    [T2Space M]
    [FiniteDimensional ℝ E] [SigmaCompactSpace M] {S B₀ B₁ : Set M}
    (hS : IsCompact S) (hB₀ : IsCompact B₀) (hB₁ : IsCompact B₁)
    (hB₀S : B₀ ⊆ S) (hB₁S : B₁ ⊆ S) (hdisj : Disjoint B₀ B₁)
    (hfrontier : frontier S = B₀ ∪ B₁)
    (hlocal₀ : ∀ b ∈ B₀, Nonempty (LocalBoundaryFunction I S B₀ b))
    (hlocal₁ : ∀ b ∈ B₁, Nonempty (LocalBoundaryFunction I S B₁ b)) :
    ∃ (O : Set M) (f : M → ℝ), IsOpen O ∧ S ⊆ O ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f O ∧
      (∀ x ∈ O, f x ∈ Icc (0 : ℝ) 1 ↔ x ∈ S) ∧
      (∀ x ∈ O, f x = 0 ↔ x ∈ B₀) ∧
      (∀ x ∈ O, f x = 1 ↔ x ∈ B₁) ∧
      (∀ x ∈ B₀ ∪ B₁, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) := by
  obtain ⟨C, h₀, h₁⟩ := exists_signedCover_of_local_boundary I
    hS hB₀ hB₁ hB₀S hB₁S hdisj hfrontier hlocal₀ hlocal₁
  exact C.exists_regular_strip_function hS.isClosed h₀ h₁

end StripFunction
end PoincareHighDim
