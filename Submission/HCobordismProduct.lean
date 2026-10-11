/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.HCobordism
import Submission.Morse.Strips.RegularBandDiffeomorph
import Mathlib.Topology.UnitInterval

/-!
# Product homeomorphisms for simply connected h-cobordism strips

Cancelling all critical points and applying the regular band theorem gives a homeomorphism
from the lower boundary times an interval onto the original cobordism strip. The map fixes
the lower boundary and identifies both boundary components with the ends of the interval.
The topological results require no additional smooth structures on these subsets. The smooth
product theorem takes the original structures as input and requires their inclusions into the
ambient manifold to be smooth immersions.
-/

namespace PoincareHighDim

open Set Topology Manifold
open scoped Manifold ContDiff

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- A simply connected homologically trivial strip of dimension at least six is homeomorphic
to its incoming boundary times the interval of level values. The homeomorphism fixes the
incoming boundary and takes exactly the two interval ends to the two boundary components. -/
theorem exists_hcobordism_band_homeomorph (h6 : 6 ≤ n)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPt I f x)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b))
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a}))
    (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    (hH : RelHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a}))) :
    ∃ Φ : (f ⁻¹' {a}) × Icc a b ≃ₜ (f ⁻¹' Icc a b),
      (∀ v : f ⁻¹' {a}, (Φ (v, ⟨a, le_rfl, hab.le⟩)).1 = v.1) ∧
      (∀ p, f (Φ p).1 = a ↔ p.2.1 = a) ∧
      (∀ p, f (Φ p).1 = b ↔ p.2.1 = b) := by
  obtain ⟨g, hmod, hg, hg_reg⟩ :=
    exists_regular_hcobordism_function I h6 f hf hab hcompact hreg hW hV₀ hV₁ hH
  have hg_compact : IsCompact (g ⁻¹' Icc a b) := by
    rw [hmod.preimage_Icc]
    exact hcompact
  obtain ⟨Ψ, hΨ, hΨa⟩ :=
    exists_regular_band_homeomorph hg hab ⟨le_rfl, hab.le⟩ hg_compact hg_reg
  let eV : (f ⁻¹' {a}) ≃ₜ (g ⁻¹' {a}) :=
    Homeomorph.setCongr hmod.preimage_singleton_left.symm
  let eW : (g ⁻¹' Icc a b) ≃ₜ (f ⁻¹' Icc a b) :=
    Homeomorph.setCongr hmod.preimage_Icc
  let Φ : (f ⁻¹' {a}) × Icc a b ≃ₜ (f ⁻¹' Icc a b) :=
    ((eV.prodCongr (Homeomorph.refl _)).trans Ψ).trans eW
  have hΦ (p : (f ⁻¹' {a}) × Icc a b) : g (Φ p).1 = p.2.1 :=
    hΨ (eV p.1, p.2)
  have hleft (x : M) : g x = a ↔ f x = a := by
    simpa only [mem_preimage, mem_singleton_iff] using
      (Set.ext_iff.mp hmod.preimage_singleton_left x)
  have hright (x : M) : g x = b ↔ f x = b := by
    simpa only [mem_preimage, mem_singleton_iff] using
      (Set.ext_iff.mp hmod.preimage_singleton_right x)
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro v
    exact hΨa (eV v)
  · intro p
    rw [← hleft, hΦ]
  · intro p
    rw [← hright, hΦ]

/-- A simply connected homologically trivial strip of dimension at least six is a product
with `[0,1]` as a topological manifold with its two distinguished ends. The product map is
the identity on the incoming boundary. -/
theorem exists_hcobordism_unitInterval_homeomorph (h6 : 6 ≤ n)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPt I f x)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b))
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a}))
    (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    (hH : RelHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a}))) :
    ∃ Φ : (f ⁻¹' {a}) × unitInterval ≃ₜ (f ⁻¹' Icc a b),
      (∀ v : f ⁻¹' {a}, (Φ (v, 0)).1 = v.1) ∧
      (∀ p, f (Φ p).1 = a ↔ p.2 = 0) ∧
      (∀ p, f (Φ p).1 = b ↔ p.2 = 1) := by
  obtain ⟨Ψ, hΨa, hΨleft, hΨright⟩ :=
    exists_hcobordism_band_homeomorph h6 hf hab hcompact hreg hW hV₀ hV₁ hH
  let eT : unitInterval ≃ₜ Icc a b := (iccHomeoI a b hab).symm
  let Φ : (f ⁻¹' {a}) × unitInterval ≃ₜ (f ⁻¹' Icc a b) :=
    ((Homeomorph.refl _).prodCongr eT).trans Ψ
  have heT0 : eT 0 = ⟨a, le_rfl, hab.le⟩ := by
    apply Subtype.ext
    simp [eT]
  have heTleft (t : unitInterval) : (eT t).1 = a ↔ t = 0 := by
    rw [iccHomeoI_symm_apply_coe]
    constructor
    · intro ht
      apply Subtype.ext
      change t.1 = 0
      nlinarith [hab]
    · intro ht
      simp [ht]
  have heTright (t : unitInterval) : (eT t).1 = b ↔ t = 1 := by
    rw [iccHomeoI_symm_apply_coe]
    constructor
    · intro ht
      apply Subtype.ext
      change t.1 = 1
      nlinarith [hab]
    · intro ht
      simp [ht]
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro v
    change (Ψ (v, eT 0)).1 = v.1
    rw [heT0]
    exact hΨa v
  · intro p
    change f (Ψ (p.1, eT p.2)).1 = a ↔ p.2 = 0
    exact (hΨleft _).trans (heTleft p.2)
  · intro p
    change f (Ψ (p.1, eT p.2)).1 = b ↔ p.2 = 1
    exact (hΨright _).trans (heTright p.2)

/-- The smooth regular-band theorem for sets identified with the level and band by equalities.
Keeping the sets separate makes it possible to retain their given smooth structures when
modifying the defining function without changing either set. -/
theorem exists_regular_band_unitInterval_diffeomorph_of_sets
    {E₀ E₁ H₀ H₁ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H₀] [TopologicalSpace H₁]
    (I₀ : ModelWithCorners ℝ E₀ H₀) (I₁ : ModelWithCorners ℝ E₁ H₁)
    {S T : Set M} [ChartedSpace H₀ S] [ChartedSpace H₁ T]
    [IsManifold I₀ ∞ S] [IsManifold I₁ ∞ T]
    {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    {a b : ℝ} [Fact (a < b)]
    (hS : S = g ⁻¹' {a}) (hT : T = g ⁻¹' Icc a b)
    (hlevel : IsImmersion I₀ I ∞ (Subtype.val : S → M))
    (hband : IsImmersion I₁ I ∞ (Subtype.val : T → M))
    (hcompact : IsCompact (g ⁻¹' Icc a b))
    (hreg : ∀ x, g x ∈ Icc a b → ¬ IsCriticalPt I g x) :
    ∃ Φ : (S × unitInterval) ≃ₘ⟮I₀.prod (𝓡∂ 1), I₁⟯ T,
      (∀ p, g (Φ p).1 = (b - a) * p.2.1 + a) ∧
      (∀ x : S, (Φ (x, 0)).1 = x.1) ∧
      (∀ x : S, g (Φ (x, 1)).1 = b) := by
  subst S
  subst T
  exact exists_regular_band_unitInterval_diffeomorph I₀ I₁ hg hlevel hband hcompact hreg

/-- A simply connected homologically trivial strip of dimension at least six is smoothly a
product for given manifold structures on the incoming level and band whose ambient inclusions
are smooth immersions. The resulting map fixes the incoming end and identifies both interval
ends exactly with the original boundary components. No product structure is assumed. -/
theorem exists_hcobordism_unitInterval_diffeomorph
    {E₀ E₁ H₀ H₁ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H₀] [TopologicalSpace H₁]
    (I₀ : ModelWithCorners ℝ E₀ H₀) (I₁ : ModelWithCorners ℝ E₁ H₁)
    (h6 : 6 ≤ n) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} [Fact (a < b)]
    [ChartedSpace H₀ (f ⁻¹' {a})] [ChartedSpace H₁ (f ⁻¹' Icc a b)]
    [IsManifold I₀ ∞ (f ⁻¹' {a})] [IsManifold I₁ ∞ (f ⁻¹' Icc a b)]
    (hlevel : IsImmersion I₀ I ∞ (Subtype.val : (f ⁻¹' {a}) → M))
    (hband : IsImmersion I₁ I ∞ (Subtype.val : (f ⁻¹' Icc a b) → M))
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPt I f x)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b))
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a}))
    (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    (hH : RelHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a}))) :
    ∃ Φ : ((f ⁻¹' {a}) × unitInterval) ≃ₘ⟮I₀.prod (𝓡∂ 1), I₁⟯ (f ⁻¹' Icc a b),
      (∀ v : f ⁻¹' {a}, (Φ (v, 0)).1 = v.1) ∧
      (∀ p, f (Φ p).1 = a ↔ p.2 = 0) ∧
      (∀ p, f (Φ p).1 = b ↔ p.2 = 1) := by
  have hab : a < b := Fact.out
  obtain ⟨g, hmod, hg, hg_reg⟩ :=
    exists_regular_hcobordism_function I h6 f hf hab hcompact hreg hW hV₀ hV₁ hH
  have hg_compact : IsCompact (g ⁻¹' Icc a b) := by
    rw [hmod.preimage_Icc]
    exact hcompact
  obtain ⟨Φ, hΦ, hΦa, -⟩ :=
    exists_regular_band_unitInterval_diffeomorph_of_sets I₀ I₁ hg
      hmod.preimage_singleton_left.symm hmod.preimage_Icc.symm
      hlevel hband hg_compact hg_reg
  have hleft (x : M) : g x = a ↔ f x = a := by
    simpa only [mem_preimage, mem_singleton_iff] using
      (Set.ext_iff.mp hmod.preimage_singleton_left x)
  have hright (x : M) : g x = b ↔ f x = b := by
    simpa only [mem_preimage, mem_singleton_iff] using
      (Set.ext_iff.mp hmod.preimage_singleton_right x)
  refine ⟨Φ, hΦa, ?_, ?_⟩
  · intro p
    rw [← hleft, hΦ]
    constructor
    · intro hp
      apply Subtype.ext
      change p.2.1 = 0
      nlinarith [hab]
    · intro hp
      simp [hp]
  · intro p
    rw [← hright, hΦ]
    constructor
    · intro hp
      apply Subtype.ext
      change p.2.1 = 1
      nlinarith [hab]
    · intro hp
      simp [hp]

end PoincareHighDim
