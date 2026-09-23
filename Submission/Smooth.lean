import Submission.HCobordism
import Submission.ModelTransport
import Submission.HomotopySphere
import Submission.Topology.TwistedSphere
import Submission.External

/-!
# The smooth high-dimensional Poincaré conjecture

Smale's theorem (Milnor, *Lectures on the h-cobordism theorem*, Proposition B; Scorpan,
*The Wild World of 4-Manifolds*, pp. 30–31): a closed smooth manifold of dimension `n ≥ 5`
homotopy equivalent to `Sⁿ` is homeomorphic to `Sⁿ`.

For `n ≥ 6` the proof is: cut out two disjoint chart disks (`exists_chartDisks_and_strip`);
the strip between them is a simply connected h-cobordism between two spheres
(`hcobordism_input_of_homotopy_sphere`, `simplyConnectedSpace_sphere`); by the h-cobordism
theorem (`hcobordism_strip`) a diffeomorphism of `M` carries the first disk onto the complement
of the second open disk, so `M` is the union of two closed disks glued along their boundaries
(a twisted sphere); the Alexander trick shows that any such space is homeomorphic to `Sⁿ`
(`twisted_sphere_homeomorph`).  The case `n = 5` is `smooth_poincare_five`.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff ContinuousMap
open Metric Set Topology

/-- **Smooth Poincaré conjecture, `n ≥ 6`** (Smale). -/
theorem poincare_smooth_ge6 {n : ℕ} (h6 : 6 ≤ n) {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin (m + 1 + 1))) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  have : Nonempty M := nonempty_of_homotopyEquiv e
  -- Step 1: two disjoint chart disks and the function `f` cutting them out.
  obtain ⟨e₀, e₁, f, h₀, h₁, hdisj, hf, hIic, hIci, hIio, hIoi, hm, hp, hreg⟩ :=
    exists_chartDisks_and_strip (M := M) (n := m + 1) (by omega : 1 ≤ m + 1)
  -- Step 2: the h-cobordism input, expressed in terms of level sets of `f`.
  obtain ⟨hW, hincl⟩ :=
    hcobordism_input_of_homotopy_sphere (by omega : 3 ≤ m + 1) e h₀ h₁ hdisj
  have hS₀ := h₀.simplyConnectedSpace_image_diskSphere (by omega : 3 ≤ m + 1)
  have hS₁ := h₁.simplyConnectedSpace_image_diskSphere (by omega : 3 ≤ m + 1)
  have hstrip : (e₀ '' diskInterior (m + 1) ∪ e₁ '' diskInterior (m + 1))ᶜ =
      f ⁻¹' Icc (-1/2) (1/2) := by
    rw [← hIio, ← hIoi]
    ext x
    simp only [mem_compl_iff, mem_union, mem_preimage, mem_Iio, mem_Ioi, mem_Icc, not_or,
      not_lt]
  rw [hstrip] at hW hincl
  rw [← hm] at hS₀ hincl
  rw [← hp] at hS₁
  -- Step 3: the h-cobordism theorem for the strip `{-1/2 ≤ f ≤ 1/2}`.
  have hf' : ContMDiff (morseModelI (m + 1)) 𝓘(ℝ, ℝ) ∞ f :=
    contMDiff_morseModelI_iff.mpr hf
  have hcompact : IsCompact (f ⁻¹' Icc (-1/2) (1/2)) :=
    (isClosed_Icc.preimage hf.continuous).isCompact
  have hreg' : ∀ x, f x = -1/2 ∨ f x = 1/2 → ¬ IsCriticalPt (morseModelI (m + 1)) f x := by
    intro x hx
    rw [isCriticalPt_morseModelI_iff hf]
    exact hreg x hx
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ := hcobordism_strip (morseModelI (m + 1)) (by omega : 6 ≤ m + 1)
    f hf' (by norm_num : (-1/2 : ℝ) < 1/2) hcompact hreg' hW hS₀ hS₁ hincl
  -- Step 4: `M` is a twisted sphere: the union of the disks `Φ ∘ e₀` and `e₁`.
  let e₀' : Disk (m + 1) → M := Φ ∘ e₀
  have h₀' : IsClosedEmbedding e₀' :=
    Φ.toHomeomorph.isClosedEmbedding.comp h₀.isClosedEmbedding
  have hrange₀ : range e₀' = f ⁻¹' Iic (1/2) := by
    change range (Φ ∘ e₀) = _
    rw [range_comp, ← hIic, hΦ₁]
  have hsph₀ : e₀' '' diskSphere (m + 1) = f ⁻¹' {1/2} := by
    change (Φ ∘ e₀) '' diskSphere (m + 1) = _
    rw [image_comp, ← hm, hΦ₂]
  have hcover : range e₀' ∪ range e₁ = univ := by
    rw [hrange₀, ← hIci]
    ext x
    simp only [mem_union, mem_preimage, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total _ _
  have hinter : range e₀' ∩ range e₁ = e₀' '' diskSphere (m + 1) := by
    rw [hrange₀, ← hIci, hsph₀]
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ici, mem_singleton_iff]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  have hbdry : e₀' '' diskSphere (m + 1) = e₁ '' diskSphere (m + 1) := by
    rw [hsph₀, hp]
  exact twisted_sphere_homeomorph h₀' h₁.isClosedEmbedding hcover hinter hbdry

/-- **Smooth Poincaré conjecture, `n ≥ 5`** (Smale; Kervaire–Milnor for `n = 5`). -/
theorem poincare_smooth {n : ℕ} (h5 : 5 ≤ n) {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  rcases Nat.eq_or_lt_of_le h5 with h | h
  · obtain rfl := h.symm
    exact smooth_poincare_five e
  · exact poincare_smooth_ge6 h e

end PoincareHighDim
