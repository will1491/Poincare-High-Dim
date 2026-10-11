/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Manifold.Cobordism.ChartPush
import Submission.Manifold.Cobordism.InwardChartPush
import Submission.Manifold.Cobordism.Extension
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Finite compositions of inward chart modifications

If a chart modification ends at the boundary, it fixes its input. Consequently,
after composing finitely many such modifications covering the compact boundary,
every point ends in the interior. The composition remains injective and smooth,
and smoothness is still detected after composition with it.
-/

namespace PoincareHighDim

open Set Topology
open scoped Manifold ContDiff

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace W] [ChartedSpace H W]
    {I : ModelWithCorners ℝ E H}

namespace ChartPushData

/-- Compose finitely many compactly supported chart modifications. -/
noncomputable def compose : List (Σ c : W, ChartPushData I c) → W → W
  | [] => id
  | d :: ds => d.2.push ∘ compose ds

@[simp] theorem compose_nil (x : W) : compose (I := I) [] x = x := rfl

@[simp] theorem compose_cons (d : Σ c : W, ChartPushData I c)
    (ds : List (Σ c : W, ChartPushData I c)) (x : W) :
    compose (d :: ds) x = d.2.push (compose ds x) := rfl

theorem compose_injective (ds : List (Σ c : W, ChartPushData I c)) :
    Function.Injective (compose ds) := by
  induction ds with
  | nil => exact Function.injective_id
  | cons d ds ih => exact d.2.injective.comp ih

variable [IsManifold I ∞ W] [T2Space W]

theorem compose_contMDiff (ds : List (Σ c : W, ChartPushData I c)) :
    ContMDiff I I ∞ (compose ds) := by
  induction ds with
  | nil => exact contMDiff_id
  | cons d ds ih => exact d.2.contMDiff.comp ih

theorem compose_isEmbedding [CompactSpace W]
    (ds : List (Σ c : W, ChartPushData I c)) : IsEmbedding (compose ds) :=
  ((compose_contMDiff ds).continuous.isClosedEmbedding (compose_injective ds)).isEmbedding

/-- Smoothness of a continuous map is detected after any finite composition of
the chart modifications, using the original manifold structure. -/
theorem compose_smooth_lift (ds : List (Σ c : W, ChartPushData I c))
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
    (J : ModelWithCorners ℝ F G) [IsManifold J ∞ N]
    {k : N → W} (hk : Continuous k)
    (hs : ContMDiff J I ∞ (fun y => compose ds (k y))) : ContMDiff J I ∞ k := by
  induction ds with
  | nil => exact hs
  | cons d ds ih =>
    apply ih
    exact d.2.smooth_lift J ((compose_contMDiff ds).continuous.comp hk) hs

omit [IsManifold I ∞ W] [T2Space W] in
/-- If the final output is a boundary point, every modification fixed the input.
This is the elementary observation that makes the finite covering argument work. -/
theorem compose_mem_boundary (ds : List (Σ c : W, ChartPushData I c))
    (hfixed : ∀ d ∈ ds, ∀ x, d.2.push x ∈ I.boundary W → d.2.push x = x)
    {x : W} (hx : compose ds x ∈ I.boundary W) :
    compose ds x = x ∧ x ∈ I.boundary W ∧
      ∀ d ∈ ds, d.2.push x ∈ I.boundary W := by
  induction ds with
  | nil => exact ⟨rfl, hx, by simp⟩
  | cons d ds ih =>
    have hhead := hfixed d (by simp) (compose ds x) hx
    have htail : compose ds x ∈ I.boundary W := by
      simpa only [compose_cons, hhead] using hx
    obtain ⟨hcomp, hxb, hall⟩ := ih (fun e he => hfixed e (by simp [he])) htail
    refine ⟨hhead.trans hcomp, hxb, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · simpa only [compose_cons, hcomp] using hx
    · exact hall e he

/-- Compactness reduces pointwise inward chart modifications to a finite
composition whose image is entirely in the manifold interior. -/
theorem exists_compose_into_interior [CompactSpace W]
    (D : ∀ x : I.boundary W, ChartPushData I x.1)
    (hactive : ∀ x, (D x).push x.1 ∈ I.interior W)
    (hfixed : ∀ x y, (D x).push y ∈ I.boundary W → (D x).push y = y) :
    ∃ ds : List (Σ c : W, ChartPushData I c), ∀ x, compose ds x ∈ I.interior W := by
  classical
  let U : I.boundary W → Set W := fun x => (D x).push ⁻¹' I.interior W
  have hU : ∀ x, IsOpen (U x) := fun x =>
    (I.isOpen_interior (n := ∞) (by simp)).preimage (D x).contMDiff.continuous
  have hcover : I.boundary W ⊆ ⋃ x, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hactive ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := (I.isClosed_boundary (n := ∞) (by simp)).isCompact.elim_finite_subcover
    U hU hcover
  let ds : List (Σ c : W, ChartPushData I c) := s.toList.map (fun x => ⟨x.1, D x⟩)
  refine ⟨ds, fun x => ?_⟩
  by_contra hx
  have hxb : compose ds x ∈ I.boundary W := by
    rw [← I.compl_interior]
    exact hx
  have hfix : ∀ d ∈ ds, ∀ y, d.2.push y ∈ I.boundary W → d.2.push y = y := by
    intro d hd
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hd
    exact hfixed z
  obtain ⟨_, hxb, hall⟩ := compose_mem_boundary ds hfix hxb
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hs hxb)
  have hmem : (⟨z.1, D z⟩ : Σ c : W, ChartPushData I c) ∈ ds :=
    List.mem_map.mpr ⟨z, Finset.mem_toList.mpr hz, rfl⟩
  have hb := hall (⟨z.1, D z⟩ : Σ c : W, ChartPushData I c) hmem
  change I.IsBoundaryPoint ((D z).push x) at hb
  change I.IsInteriorPoint ((D z).push x) at hxz
  exact (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint (I := I) _).mp hxz hb

end ChartPushData

/-- A finite collection of coordinate modifications moving the entire manifold
into its own interior. The smoothness and inverse compatibility are consequences
of the coordinate construction, not additional assumptions. -/
structure InwardCopy (I : ModelWithCorners ℝ E H) (W : Type*) [TopologicalSpace W]
    [ChartedSpace H W] where
  modifications : List (Σ c : W, ChartPushData I c)
  image_interior : ∀ x, ChartPushData.compose modifications x ∈ I.interior W

/-- Every compact smooth manifold with boundary has a smooth copy inside its own
interior, constructed using finitely many supported coordinate displacements. -/
theorem nonempty_inwardCopy {n : ℕ} {W : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W] [CompactSpace W] [T2Space W] :
    Nonempty (InwardCopy (𝓡∂ (n + 1)) W) := by
  classical
  choose D hactive hfixed using exists_inward_chartPush (n := n) (W := W)
  obtain ⟨ds, hds⟩ := ChartPushData.exists_compose_into_interior D hactive hfixed
  exact ⟨⟨ds, hds⟩⟩

namespace InwardCopy

variable {n : ℕ} {W : Type*} [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (𝓡∂ (n + 1)) ∞ W] [CompactSpace W] [T2Space W]
    (C : InwardCopy (𝓡∂ (n + 1)) W)

/-- The inclusion of the constructed copy into the boundaryless interior. -/
noncomputable def embedding (x : W) : (𝓡∂ (n + 1)).interior W :=
  ⟨ChartPushData.compose C.modifications x, C.image_interior x⟩

omit [CompactSpace W] in
theorem continuous_embedding : Continuous C.embedding :=
  (ChartPushData.compose_contMDiff C.modifications).continuous.subtype_mk _

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] [CompactSpace W] [T2Space W] in
theorem injective_embedding : Function.Injective C.embedding := by
  intro x y h
  exact ChartPushData.compose_injective C.modifications (congrArg Subtype.val h)

theorem isEmbedding : IsEmbedding C.embedding :=
  (C.continuous_embedding.isClosedEmbedding C.injective_embedding).isEmbedding

omit [CompactSpace W] in
theorem contMDiff_embedding :
    letI := (ManifoldInterior.inducedAtlas (𝓡∂ (n + 1)) (W := W)).chartedSpace
    ContMDiff (𝓡∂ (n + 1)) (interiorModel (n + 1)) ∞ C.embedding := by
  let := (ManifoldInterior.inducedAtlas (𝓡∂ (n + 1)) (W := W)).chartedSpace
  exact (contMDiff_into_interior_iff (𝓡∂ (n + 1))).mpr
    ⟨C.continuous_embedding, ChartPushData.compose_contMDiff C.modifications⟩

omit [CompactSpace W] in
/-- The constructed copy has exactly the original smooth structure on `W`. -/
theorem smooth_lift
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
    (J : ModelWithCorners ℝ F G) [IsManifold J ∞ N]
    {k : N → W} (hk : Continuous k) :
    letI := (ManifoldInterior.inducedAtlas (𝓡∂ (n + 1)) (W := W)).chartedSpace
    ContMDiff J (interiorModel (n + 1)) ∞ (C.embedding ∘ k) →
      ContMDiff J (𝓡∂ (n + 1)) ∞ k := by
  let := (ManifoldInterior.inducedAtlas (𝓡∂ (n + 1)) (W := W)).chartedSpace
  intro hs
  exact ChartPushData.compose_smooth_lift C.modifications J hk
    (contMDiff_interior_inclusion.comp hs)

end InwardCopy

end PoincareHighDim
