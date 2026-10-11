/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Topology.Engulfing.MapEngulfingSequence
import Submission.Topology.Engulfing.Simplex.Columns.ColumnPreimage

/-!
# The relative complexity in Newman's induction

The complexity index is a bound on the number of vertices of a subcomplex
containing the part of the target not yet mapped into the current open set.
Index zero is the empty exceptional set. The source map and its fixed subcomplex
remain explicit, as required for the later dimension induction.
-/

namespace PoincareHighDim.Engulfing

open Set Geometry Topology
open scoped ContinuousMap

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M]

/-- All target points outside the current open set lie in a subcomplex of
dimension at most `q - 1`. The convention `q = 0` means there are none. -/
def EngulfingOutsideDimension (K H : SimplicialComplex ℝ E)
    (f : C(K.space, M)) (U : Set M) (q : ℕ) : Prop :=
  ∃ Q : SimplicialComplex ℝ E, Q.faces ⊆ H.faces ∧
    (∀ s ∈ Q.faces, s.card ≤ q) ∧
    ∀ x : K.space, x.1 ∈ H.space → x.1 ∉ Q.space → f x ∈ U

/-- The stronger combinatorial form used for the actual induction: the target
is a union of a covered subcomplex and a subcomplex of the indicated dimension.
This form makes the remaining top-dimensional simplices principal faces. -/
def EngulfingDecomposition (K H : SimplicialComplex ℝ E)
    (f : C(K.space, M)) (U : Set M) (q : ℕ) : Prop :=
  ∃ R Q : SimplicialComplex ℝ E,
    R.faces ⊆ H.faces ∧ Q.faces ⊆ H.faces ∧ H.faces = R.faces ∪ Q.faces ∧
    (∀ s ∈ Q.faces, s.card ≤ q) ∧
    ∀ x : K.space, x.1 ∈ R.space → f x ∈ U

theorem EngulfingDecomposition.to_outsideDimension {K H : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {U : Set M} {q : ℕ}
    (h : EngulfingDecomposition K H f U q) : EngulfingOutsideDimension K H f U q := by
  obtain ⟨R, Q, _, hQH, hfaces, hdim, hR⟩ := h
  refine ⟨Q, hQH, hdim, ?_⟩
  intro x hx hnot
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  rw [hfaces] at hs
  rcases hs with hs | hs
  · exact hR x (R.convexHull_subset_space hs hxs)
  · exact (hnot (Q.convexHull_subset_space hs hxs)).elim

/-- The initial target always has a decomposition with empty covered part. -/
theorem engulfingDecomposition_of_face_card_le (K H : SimplicialComplex ℝ E)
    (f : C(K.space, M)) (U : Set M) {q : ℕ}
    (hdim : ∀ s ∈ H.faces, s.card ≤ q) : EngulfingDecomposition K H f U q := by
  refine ⟨⊥, H, empty_subset _, subset_rfl, ?_, hdim, ?_⟩
  · rw [SimplicialComplex.faces_bot, empty_union]
  · intro x hx
    rw [SimplicialComplex.space_bot] at hx
    exact hx.elim

/-- An uncovered simplex at the top remaining dimension cannot be a proper
face of another target simplex. -/
theorem EngulfingDecomposition.principal_of_uncovered {K H : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {U : Set M} {q : ℕ}
    (h : EngulfingDecomposition K H f U q) {s : Finset E} (hcard : q ≤ s.card)
    (huncovered : ∃ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) ∧ f x ∉ U) :
    ∀ t ∈ H.faces, s ⊆ t → t = s := by
  obtain ⟨R, Q, _, _, hfaces, hdim, hR⟩ := h
  intro t ht hst
  rw [hfaces] at ht
  rcases ht with ht | ht
  · obtain ⟨x, hxs, hnot⟩ := huncovered
    exact (hnot (hR x (R.convexHull_subset_space ht (convexHull_mono hst hxs)))).elim
  · exact (Finset.eq_of_subset_of_card_le hst ((hdim t ht).trans hcard)).symm

/-- The result required by the relative engulfing induction. -/
def NewmanConclusion (K L H : SimplicialComplex ℝ E) (f : C(K.space, M))
    (X U : Set M) (ε : ℝ) : Prop :=
  ∃ (g : C(K.space, M)) (h : M ≃ₜ M),
    (∀ x : K.space, x.1 ∈ L.space → g x = f x) ∧
    (∀ x, dist (g x) (f x) < ε) ∧
    X ∪ g '' (Subtype.val ⁻¹' H.space) ⊆ h '' U ∧
    IsCompact (closure {x | h x ≠ x})

theorem EngulfingOutsideDimension.mono_index {K H : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {U : Set M} {q r : ℕ}
    (h : EngulfingOutsideDimension K H f U q) (hqr : q ≤ r) :
    EngulfingOutsideDimension K H f U r := by
  obtain ⟨Q, hQH, hdim, hcover⟩ := h
  exact ⟨Q, hQH, fun s hs => (hdim s hs).trans hqr, hcover⟩

theorem EngulfingOutsideDimension.mono_open {K H : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {U V : Set M} {q : ℕ}
    (h : EngulfingOutsideDimension K H f U q) (hUV : U ⊆ V) :
    EngulfingOutsideDimension K H f V q := by
  obtain ⟨Q, hQH, hdim, hcover⟩ := h
  exact ⟨Q, hQH, hdim, fun x hx hnot => hUV (hcover x hx hnot)⟩

/-- This is the dimension-decrease criterion: all newly required points are in
a small-dimensional subcomplex, and all other target points are already covered. -/
theorem engulfingOutsideDimension_of_cover (K H R Q : SimplicialComplex ℝ E)
    (f : C(K.space, M)) {U : Set M} {q : ℕ}
    (hQH : Q.faces ⊆ H.faces) (hdim : ∀ s ∈ Q.faces, s.card ≤ q)
    (hcover : H.space ⊆ R.space ∪ Q.space)
    (hR : ∀ x : K.space, x.1 ∈ R.space → f x ∈ U) :
    EngulfingOutsideDimension K H f U q := by
  refine ⟨Q, hQH, hdim, ?_⟩
  intro x hx hnot
  exact hR x ((hcover hx).resolve_right hnot)

/-- A zero-dimensional complexity index has an empty exceptional subcomplex. -/
theorem EngulfingOutsideDimension.zero_covered {K H : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {U : Set M}
    (h : EngulfingOutsideDimension K H f U 0) :
    f '' (Subtype.val ⁻¹' H.space) ⊆ U := by
  obtain ⟨Q, _, hdim, hcover⟩ := h
  have hQempty : Q.space = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨s, hs, _⟩ := SimplicialComplex.mem_space_iff.mp hx
    have hpos := Finset.card_pos.mpr (Q.nonempty_of_mem_faces hs)
    have hz := hdim s hs
    omega
  rintro y ⟨x, hx, rfl⟩
  exact hcover x hx (by rw [hQempty]; simp)

/-- The base case of the relative dimension induction requires no motion or
perturbation and has empty support. -/
theorem newmanConclusion_of_zero_complexity (K L H : SimplicialComplex ℝ E)
    (f : C(K.space, M)) {X U : Set M} (hX : X ⊆ U)
    (hzero : EngulfingOutsideDimension K H f U 0) {ε : ℝ} (hε : 0 < ε) :
    NewmanConclusion K L H f X U ε := by
  refine ⟨f, Homeomorph.refl M, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro x
    simpa only [dist_self] using hε
  · intro x hx
    refine ⟨x, ?_, rfl⟩
    exact hx.elim (fun h => hX h) (fun h => hzero.zero_covered h)
  · simp

end PoincareHighDim.Engulfing
