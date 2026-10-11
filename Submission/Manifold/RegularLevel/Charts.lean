/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.RegularLevel.Atlas
import Submission.Manifold.RegularLevel.SmoothAtlas
import Submission.Morse.Handles.Partners.PartnerEngines

/-!
# Induced charts on a regular level

An adapted ambient chart identifies a regular level with a coordinate hyperplane.
Deleting the distinguished coordinate gives a chart of the expected dimension. Both
directions are related explicitly to smooth ambient maps.
-/

namespace PoincareHighDim

open Set Topology
open scoped Manifold ContDiff

namespace RegularLevel

noncomputable section

/-- Inserting a zero coordinate is smooth. -/
theorem contDiff_insertZero {m : ℕ} (i : Fin (m + 1)) :
    ContDiff ℝ ∞ (fun v : Fin m → ℝ => i.insertNth (α := fun _ => ℝ) 0 v) := by
  apply contDiff_pi.mpr
  intro j
  rcases i.eq_self_or_eq_succAbove j with rfl | ⟨k, rfl⟩
  · simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin m → ℝ => (0 : ℝ)))
  · simpa using (contDiff_apply ℝ ℝ k : ContDiff ℝ ∞ (fun v : Fin m → ℝ => v k))

/-- Deleting one coordinate is smooth. -/
theorem contDiff_removeNth {m : ℕ} (i : Fin (m + 1)) :
    ContDiff ℝ ∞ (i.removeNth : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) := by
  apply contDiff_pi.mpr
  intro j
  exact contDiff_apply ℝ ℝ (i.succAbove j)

/-- A coordinate hyperplane has its usual Euclidean coordinates. -/
def hyperplaneHomeomorph {m : ℕ} (i : Fin (m + 1)) :
    (Fin m → ℝ) ≃ₜ {v : Fin (m + 1) → ℝ | v i = 0} where
  toFun v := ⟨i.insertNth (α := fun _ => ℝ) 0 v, by simp⟩
  invFun v := i.removeNth v.1
  left_inv v := by simp
  right_inv v := by
    apply Subtype.ext
    change i.insertNth (α := fun _ => ℝ) 0 (i.removeNth v.1) = v.1
    have hv : v.1 i = 0 := v.2
    have h := i.insertNth_self_removeNth v.1
    rwa [hv] at h
  continuous_toFun := (contDiff_insertZero i).continuous.subtype_mk _
  continuous_invFun := (contDiff_removeNth i).continuous.comp continuous_subtype_val

variable {m : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin (m + 1) → ℝ) H}
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

/-- A regular level admits charts of codimension one whose coordinate maps extend
smoothly to ambient open sets and whose inverse parametrizations are ambient-smooth. -/
theorem exists_chart {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {c : ℝ} (hreg : ∀ x, f x = c → ¬ IsCriticalPt I f x)
    (x : f ⁻¹' {c}) :
    ∃ (e : OpenPartialHomeomorph (f ⁻¹' {c}) (Fin m → ℝ))
      (U : Set M) (ext : M → (Fin m → ℝ)),
      x ∈ e.source ∧ IsOpen U ∧ e.source = Subtype.val ⁻¹' U ∧
      (∀ y ∈ e.source, e y = ext y.1) ∧
      ContMDiffOn I 𝓘(ℝ, Fin m → ℝ) ∞ ext U ∧
      ContMDiffOn 𝓘(ℝ, Fin m → ℝ) I ∞
        (fun v => (e.symm v).1) e.target := by
  classical
  have hx : f x.1 = c := x.2
  obtain ⟨ψ, i, r, hr, hball, hψ0, hψ, hψs, hψf⟩ :=
    IndexOnePartner.exists_levelChart hf (hreg x.1 hx)
  let S : Set (Fin (m + 1) → ℝ) := {v | v i = 0}
  have hImage : ψ.IsImage S (f ⁻¹' {c}) := by
    intro v hv
    change f (ψ v) = c ↔ v i = 0
    rw [hψf v hv, hx]
    exact add_eq_left
  have : Nonempty S := ⟨⟨0, rfl⟩⟩
  have : Nonempty (f ⁻¹' {c}) := ⟨x⟩
  let C := hImage.subtype
  let L := hyperplaneHomeomorph i
  let e := C.symm.trans L.symm.toOpenPartialHomeomorph
  have hsource : e.source = Subtype.val ⁻¹' ψ.target := by
    simp [e, C]
  have htarget : e.target = (fun v => i.insertNth (α := fun _ => ℝ) 0 v) ⁻¹' ψ.source := by
    ext v
    simp [e, C, L, hyperplaneHomeomorph]
  have hExt (y : f ⁻¹' {c}) (hy : y ∈ e.source) :
      e y = i.removeNth (ψ.symm y.1) := by
    have hy' : y.1 ∈ ψ.target := by rwa [hsource] at hy
    change i.removeNth (C.symm y).1 = i.removeNth (ψ.symm y.1)
    rw [hImage.subtype_symm_apply_val hy']
  have hInv (v : Fin m → ℝ) (hv : v ∈ e.target) :
      (e.symm v).1 = ψ (i.insertNth (α := fun _ => ℝ) 0 v) := by
    have hv' : i.insertNth (α := fun _ => ℝ) 0 v ∈ ψ.source := by rwa [htarget] at hv
    change (C (L v)).1 = ψ (i.insertNth (α := fun _ => ℝ) 0 v)
    exact hImage.subtype_apply_val hv'
  refine ⟨e, ψ.target, fun y => i.removeNth (ψ.symm y), ?_, ψ.open_target,
    hsource, hExt, ?_, ?_⟩
  · rw [hsource]
    have h0 : (0 : Fin (m + 1) → ℝ) ∈ ψ.source := hball (Metric.mem_ball_self hr)
    simpa [hψ0] using ψ.map_source h0
  · exact (contDiff_removeNth i).contMDiff.comp_contMDiffOn hψs
  · apply ContMDiffOn.congr _ hInv
    apply hψ.comp (contDiff_insertZero i).contMDiff.contMDiffOn
    intro v hv
    exact htarget ▸ hv

/-- The smooth atlas on a regular level obtained by restricting adapted ambient charts.
Its transition maps and its compatibility with the ambient smooth structure follow from
the explicit ambient extensions recorded in `InducedAtlas`. -/
def inducedAtlas {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {c : ℝ} (hreg : ∀ x, f x = c → ¬ IsCriticalPt I f x) :
    InducedAtlas I (f ⁻¹' {c}) (Fin m → ℝ) := by
  classical
  choose e U ext hmem hopen hsource hext hsmooth hinverse using exists_chart hf hreg
  exact
    { chart := e
      mem_source := hmem
      ambientSource := U
      open_ambientSource := hopen
      source_eq := hsource
      extension := ext
      extension_eq := fun x y hy => (hext x y hy).symm
      smooth_extension := hsmooth
      smooth_inverse := hinverse }

end

end RegularLevel

end PoincareHighDim
