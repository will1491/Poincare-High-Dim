/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.HCobordism
import Submission.Manifold.RegularLevel.Charts
import Submission.Manifold.RegularLevel.Band

/-!
# Smooth products for simply connected h-cobordism strips

The compact strip and its incoming boundary carry their induced smooth structures, and
the strip is diffeomorphic to that boundary times the unit interval. These smooth structures
are constructed, not assumed. Their compatibility with the ambient manifold is certified by
smooth inclusion and by a criterion detecting smoothness through the ambient inclusion.

This theorem concerns cobordisms already presented as regular-boundary strips in a smooth
ambient manifold. It does not assume or assert a representation theorem for arbitrary
abstract manifolds with boundary.
-/

namespace PoincareHighDim

open Set Topology Manifold
open scoped Manifold ContDiff

universe uM

section Structures

variable {E H : Type*} {E₀ H₀ : Type} {M : Type uM}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [TopologicalSpace H] [TopologicalSpace H₀]
    [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (I₀ : ModelWithCorners ℝ E₀ H₀)

/-- A smooth subspace structure whose smooth maps are detected by the original ambient
smooth structure. The lifting field rules out introducing an unrelated smooth structure
through a chosen topological parametrization. -/
structure InducedSmoothStructure (s : Set M) where
  chartedSpace : ChartedSpace H₀ s
  isManifold : letI := chartedSpace; IsManifold I₀ ∞ s
  smooth_inclusion : letI := chartedSpace;
    ContMDiff I₀ I ∞ (Subtype.val : s → M)
  smooth_lift :
    ∀ {EN HN : Type} {N : Type uM} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
      [TopologicalSpace HN] [TopologicalSpace N] [ChartedSpace HN N]
      (J : ModelWithCorners ℝ EN HN) [IsManifold J ∞ N] (k : N → s),
      letI := chartedSpace;
      Continuous k → ContMDiff J I ∞ (fun x => (k x).1) → ContMDiff J I₀ ∞ k

/-- Product coordinates compatible with the ambient smooth structure, with the incoming
boundary fixed and both distinguished boundaries identified exactly. -/
structure InducedSmoothProduct (S W U : Set M) where
  incoming : InducedSmoothStructure I I₀ S
  cobordism : InducedSmoothStructure I (I₀.prod (𝓡∂ 1)) W
  diffeomorph :
    letI := incoming.chartedSpace
    letI := cobordism.chartedSpace
    (S × unitInterval) ≃ₘ⟮I₀.prod (𝓡∂ 1), I₀.prod (𝓡∂ 1)⟯ W
  fixes_incoming : ∀ v : S, (diffeomorph (v, 0)).1 = v.1
  incoming_iff : ∀ p, (diffeomorph p).1 ∈ S ↔ p.2 = 0
  outgoing_iff : ∀ p, (diffeomorph p).1 ∈ U ↔ p.2 = 1

end Structures

namespace InducedSmoothStructure

variable {E H : Type*} {E₀ E₁ H₀ H₁ : Type} {M : Type uM}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H] [TopologicalSpace H₀] [TopologicalSpace H₁]
    [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H}
    {I₀ : ModelWithCorners ℝ E₀ H₀} {I₁ : ModelWithCorners ℝ E₁ H₁} {s : Set M}

/-- Any two smooth structures induced by the same ambient manifold agree: the identity
map on the subspace is a diffeomorphism. The two charted-space arguments are written
explicitly because they are structures on the same underlying type. -/
def identityDiffeomorph (A : InducedSmoothStructure I I₀ s)
    (B : InducedSmoothStructure I I₁ s) :
    @Diffeomorph ℝ _ E₀ _ _ E₁ _ _ H₀ _ H₁ _ I₀ I₁
      s _ A.chartedSpace s _ B.chartedSpace ∞ := by
  letI := A.chartedSpace
  letI := B.chartedSpace
  refine ⟨Equiv.refl s, ?_, ?_⟩
  · let := A.chartedSpace
    let := A.isManifold
    exact B.smooth_lift I₀ id continuous_id A.smooth_inclusion
  · let := B.chartedSpace
    let := B.isManifold
    exact A.smooth_lift I₁ id continuous_id B.smooth_inclusion

@[simp] theorem identityDiffeomorph_apply (A : InducedSmoothStructure I I₀ s)
    (B : InducedSmoothStructure I I₁ s) (x : s) : A.identityDiffeomorph B x = x := rfl

/-- A given smooth submanifold structure, expressed by an immersion of its inclusion,
has the ambient smoothness-detection property. -/
def ofImmersion [ChartedSpace H₀ s] [IsManifold I₀ ∞ s]
    (h : IsImmersion I₀ I ∞ (Subtype.val : s → M)) : InducedSmoothStructure I I₀ s where
  chartedSpace := inferInstance
  isManifold := inferInstance
  smooth_inclusion := h.contMDiff
  smooth_lift := by
    intro EN HN N _ _ _ _ _ J _ k hk hs
    exact (ContMDiff.iff_comp_isImmersion h).mpr ⟨hk, hs⟩

end InducedSmoothStructure

namespace InducedAtlas

variable {E H : Type*} {E₀ : Type} {M : Type uM}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M] {s : Set M}

/-- An atlas with smooth ambient extensions supplies the induced smooth subspace structure. -/
def toInducedSmoothStructure (A : InducedAtlas I s E₀) :
    InducedSmoothStructure I 𝓘(ℝ, E₀) s where
  chartedSpace := A.chartedSpace
  isManifold := A.isManifold
  smooth_inclusion := A.contMDiff_subtypeVal
  smooth_lift := by
    intro EN HN N _ _ _ _ _ J _ k hk hs
    exact (A.contMDiff_iff J).mpr ⟨hk, hs⟩

end InducedAtlas

section RegularBand

variable {m : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin (m + 1) → ℝ) H}
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- A compact band with no critical points is smoothly a product with its induced smooth
structures. No smooth structures on the level or band occur among the hypotheses. -/
theorem nonempty_regular_band_inducedSmoothProduct
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x ∈ Icc a b → ¬ IsCriticalPt I f x) :
    Nonempty (InducedSmoothProduct I 𝓘(ℝ, Fin m → ℝ)
      (f ⁻¹' {a}) (f ⁻¹' Icc a b) (f ⁻¹' {b})) := by
  classical
  have : Fact (a < b) := ⟨hab⟩
  let A := RegularLevel.inducedAtlas hf (c := a) (fun x hx =>
    hreg x (by rw [hx]; exact ⟨le_rfl, hab.le⟩))
  let L := A.toInducedSmoothStructure
  let := L.chartedSpace
  let := L.isManifold
  obtain ⟨C⟩ := RegularBand.nonempty_flowCoordinates hf hab hcompact hreg
  let B : InducedSmoothStructure I (𝓘(ℝ, Fin m → ℝ).prod (𝓡∂ 1))
      (f ⁻¹' Icc a b) :=
    { chartedSpace := C.chartedSpace
      isManifold := C.isManifold 𝓘(ℝ, Fin m → ℝ)
      smooth_inclusion := C.contMDiff_subtypeVal 𝓘(ℝ, Fin m → ℝ) L.smooth_inclusion
      smooth_lift := by
        intro EN HN N _ _ _ _ _ J _ k hk hs
        exact (C.contMDiff_iff 𝓘(ℝ, Fin m → ℝ) J hf L.smooth_inclusion
          (fun k hk hs => L.smooth_lift J k hk hs)).mpr ⟨hk, hs⟩ }
  let := B.chartedSpace
  let := B.isManifold
  obtain ⟨Φ, hΦ, hΦa, -⟩ := exists_regular_band_unitInterval_diffeomorph_of_lifting
    𝓘(ℝ, Fin m → ℝ) (𝓘(ℝ, Fin m → ℝ).prod (𝓡∂ 1)) hf
    L.smooth_inclusion B.smooth_inclusion
    (fun k hk hs => L.smooth_lift _ k hk hs)
    (fun k hk hs => B.smooth_lift _ k hk hs) hcompact hreg
  refine ⟨{
    incoming := L
    cobordism := B
    diffeomorph := Φ
    fixes_incoming := hΦa
    incoming_iff := ?_
    outgoing_iff := ?_ }⟩
  · intro p
    change f (Φ p).1 = a ↔ p.2 = 0
    rw [hΦ]
    constructor
    · intro hp
      apply Subtype.ext
      change p.2.1 = 0
      nlinarith [hab]
    · intro hp
      simp [hp]
  · intro p
    change f (Φ p).1 = b ↔ p.2 = 1
    rw [hΦ]
    constructor
    · intro hp
      apply Subtype.ext
      change p.2.1 = 1
      nlinarith [hab]
    · intro hp
      simp [hp]

/-- A simply connected homologically trivial compact strip of dimension at least six is
diffeomorphic to its incoming boundary times `[0,1]`, with the induced smooth structures.
The incoming end is fixed pointwise, and the two ends are exactly the original two levels. -/
theorem nonempty_hcobordism_inducedSmoothProduct (h6 : 6 ≤ m + 1)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ IsCriticalPt I f x)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b))
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a}))
    (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    (hH : RelHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a}))) :
    Nonempty (InducedSmoothProduct I 𝓘(ℝ, Fin m → ℝ)
      (f ⁻¹' {a}) (f ⁻¹' Icc a b) (f ⁻¹' {b})) := by
  obtain ⟨g, hmod, hg, hg_reg⟩ :=
    exists_regular_hcobordism_function I h6 f hf hab hcompact hreg hW hV₀ hV₁ hH
  have hg_compact : IsCompact (g ⁻¹' Icc a b) := by
    rw [hmod.preimage_Icc]
    exact hcompact
  have hprod := nonempty_regular_band_inducedSmoothProduct hg hab hg_compact hg_reg
  rwa [hmod.preimage_singleton_left, hmod.preimage_Icc,
    hmod.preimage_singleton_right] at hprod

end RegularBand

end PoincareHighDim
