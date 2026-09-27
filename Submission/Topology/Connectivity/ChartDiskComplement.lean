import Submission.HomotopySphere

/-!
# The complement of one open chart disk

Removing an open chart disk from a simply connected manifold of dimension at least three
preserves simple connectivity. The proof pushes paths and null-homotopies out of the disk,
using `IsChartDisk.exists_push_off`.

For a compact homotopy sphere, the complement is also acyclic. The final theorem packages
these two properties without using Whitehead's theorem or a contractibility assumption.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff ContinuousMap
open Metric Set Topology unitInterval

universe u

/-- Pushing a square out of a chart disk preserves every ambient subset containing that disk. -/
theorem IsChartDisk.exists_push_off_within {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : Disk n → M} (he : IsChartDisk e) {B : Set M} (hD : range e ⊆ B)
    {F : I × I → M} (hF : Continuous F) (hFB : ∀ z, F z ∈ B) :
    ∃ F' : I × I → M, Continuous F' ∧ (∀ z, F' z ∈ B \ e '' diskInterior n) ∧
      (∀ z, F z ∉ e '' diskInterior n → F' z = F z) := by
  obtain ⟨F', hF', hmem, hfix, hin⟩ := he.exists_push_off hn hF
  refine ⟨F', hF', fun z => ⟨?_, hmem z⟩, hfix⟩
  by_cases hz : F z ∈ e '' diskInterior n
  · exact hD (hin z hz)
  · rw [hfix z hz]
    exact hFB z

/-- Removing an open chart disk from a path connected subset containing the closed disk
preserves path connectivity in dimension at least three. -/
theorem isPathConnected_sdiff_chartDisk {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : Disk n → M} (he : IsChartDisk e) {B : Set M} (hD : range e ⊆ B)
    (hB : IsPathConnected B) : IsPathConnected (B \ e '' diskInterior n) := by
  rw [isPathConnected_iff]
  refine ⟨?_, fun x hx y hy => ?_⟩
  · let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ 1
    have hv : ‖v‖ = 1 := by simp [v]
    let w : Disk n := ⟨v, mem_closedBall_zero_iff.2 hv.le⟩
    refine ⟨e w, hD (mem_range_self w), ?_⟩
    intro h
    rw [he.injective.mem_set_image, mem_diskInterior] at h
    exact absurd h (by simp [w, hv])
  · obtain ⟨γ, hγ⟩ := hB.joinedIn x hx.1 y hy.1
    obtain ⟨F', hF', hmem, hfix⟩ := he.exists_push_off_within hn hD
      (F := fun z : I × I => γ z.2) (γ.continuous.comp continuous_snd) (fun z => hγ z.2)
    refine ⟨⟨⟨fun s => F' (0, s), hF'.comp (continuous_const.prodMk continuous_id)⟩,
      ?_, ?_⟩, fun t => hmem (0, t)⟩
    · show F' (0, 0) = x
      rw [hfix (0, 0) (by show γ 0 ∉ _; rw [γ.source]; exact hx.2)]
      exact γ.source
    · show F' (0, 1) = y
      rw [hfix (0, 1) (by show γ 1 ∉ _; rw [γ.target]; exact hy.2)]
      exact γ.target

/-- Removing an open chart disk from a simply connected subset containing the closed disk
preserves simple connectivity in dimension at least three. No manifold structure on the
subset itself is needed. -/
theorem isSimplyConnected_sdiff_chartDisk {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : Disk n → M} (he : IsChartDisk e) {B : Set M} (hD : range e ⊆ B)
    (hB : IsSimplyConnected B) : IsSimplyConnected (B \ e '' diskInterior n) := by
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem] at hB ⊢
  refine ⟨isPathConnected_sdiff_chartDisk hn he hD hB.1, fun x p hp => ?_⟩
  obtain ⟨G, hG⟩ := hB.2 x p (fun t => (hp t).1)
  obtain ⟨F', hF', hmem, hfix⟩ := he.exists_push_off_within hn hD
    (F := fun z : I × I => G z) G.continuous hG
  have hx : x ∉ e '' diskInterior n := p.source ▸ (hp 0).2
  refine ⟨{ toFun := F'
            continuous_toFun := hF'
            map_zero_left := fun s => ?_
            map_one_left := fun s => ?_
            prop' := fun t s hs => ?_ }, hmem⟩
  · rw [hfix (0, s) (by show G (0, s) ∉ _; rw [G.apply_zero]; exact (hp s).2)]
    exact G.apply_zero s
  · rw [hfix (1, s) (by show G (1, s) ∉ _; rw [G.apply_one]; exact hx)]
    exact G.apply_one s
  · rcases hs with rfl | rfl
    · show F' (t, 0) = p 0
      rw [hfix (t, 0) (by show G (t, 0) ∉ _; rw [G.source]; exact hx)]
      show G (t, 0) = p 0
      rw [G.source, p.source]
    · show F' (t, 1) = p 1
      rw [hfix (t, 1) (by show G (t, 1) ∉ _; rw [G.target]; exact hx)]
      show G (t, 1) = p 1
      rw [G.target, p.target]

/-- The complement of an open chart disk in a path connected manifold of dimension at least
three is path connected. -/
theorem isPathConnected_compl_chartDisk {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [PathConnectedSpace M] {e : Disk n → M} (he : IsChartDisk e) :
    IsPathConnected ((e '' diskInterior n)ᶜ : Set M) := by
  rw [isPathConnected_iff]
  refine ⟨?_, fun x hx y hy => ?_⟩
  · let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ 1
    have hv : ‖v‖ = 1 := by simp [v]
    let w : Disk n := ⟨v, mem_closedBall_zero_iff.2 hv.le⟩
    refine ⟨e w, ?_⟩
    intro h
    rw [he.injective.mem_set_image, mem_diskInterior] at h
    exact absurd h (by simp [w, hv])
  · let γ := PathConnectedSpace.somePath x y
    obtain ⟨F', hF', hmem, hfix, -⟩ := he.exists_push_off hn
      (F := fun z : I × I => γ z.2) (γ.continuous.comp continuous_snd)
    refine ⟨⟨⟨fun s => F' (0, s), hF'.comp (continuous_const.prodMk continuous_id)⟩,
      ?_, ?_⟩, fun t => hmem (0, t)⟩
    · show F' (0, 0) = x
      rw [hfix (0, 0) (by show γ 0 ∉ _; rw [γ.source]; exact hx)]
      exact γ.source
    · show F' (0, 1) = y
      rw [hfix (0, 1) (by show γ 1 ∉ _; rw [γ.target]; exact hy)]
      exact γ.target

/-- A loop outside an open chart disk in a simply connected manifold of dimension at least
three has a null-homotopy outside the disk. -/
theorem exists_homotopy_refl_compl_chartDisk {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SimplyConnectedSpace M] {e : Disk n → M} (he : IsChartDisk e) (x : M) (p : Path x x)
    (hp : ∀ t, p t ∈ (e '' diskInterior n)ᶜ) :
    ∃ F : p.Homotopy (.refl x), ∀ t, F t ∈ (e '' diskInterior n)ᶜ := by
  obtain ⟨G⟩ := SimplyConnectedSpace.paths_homotopic p (Path.refl x)
  obtain ⟨F', hF', hmem, hfix, -⟩ := he.exists_push_off hn
    (F := fun z : I × I => G z) G.continuous
  have hx : x ∈ (e '' diskInterior n)ᶜ := p.source ▸ hp 0
  refine ⟨{ toFun := F'
            continuous_toFun := hF'
            map_zero_left := fun s => ?_
            map_one_left := fun s => ?_
            prop' := fun t s hs => ?_ }, hmem⟩
  · rw [hfix (0, s) (by show G (0, s) ∉ _; rw [G.apply_zero]; exact hp s)]
    exact G.apply_zero s
  · rw [hfix (1, s) (by show G (1, s) ∉ _; rw [G.apply_one]; exact hx)]
    exact G.apply_one s
  · rcases hs with rfl | rfl
    · show F' (t, 0) = p 0
      rw [hfix (t, 0) (by show G (t, 0) ∉ _; rw [G.source]; exact hx)]
      show G (t, 0) = p 0
      rw [G.source, p.source]
    · show F' (t, 1) = p 1
      rw [hfix (t, 1) (by show G (t, 1) ∉ _; rw [G.target]; exact hx)]
      show G (t, 1) = p 1
      rw [G.target, p.target]

/-- Removing one open chart disk preserves simple connectivity in dimension at least three. -/
theorem simplyConnectedSpace_compl_chartDisk {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SimplyConnectedSpace M] {e : Disk n → M} (he : IsChartDisk e) :
    SimplyConnectedSpace ((e '' diskInterior n)ᶜ : Set M) := by
  change IsSimplyConnected _
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  exact ⟨isPathConnected_compl_chartDisk hn he,
    exists_homotopy_refl_compl_chartDisk hn he⟩

/-- The complement of an open chart disk in a compact homotopy sphere of dimension at least
three is simply connected and has vanishing reduced integral homology. -/
theorem simplyConnected_acyclic_compl_chartDisk_of_homotopy_sphere {n : ℕ} (hn : 3 ≤ n)
    {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    {d : Disk n → M} (hd : IsChartDisk d) :
    SimplyConnectedSpace ((d '' diskInterior n)ᶜ : Set M) ∧
      SingularPair.Acyclic SingularPair.Z.{u} (TopCat.of ((d '' diskInterior n)ᶜ : Set M)) := by
  have : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    simplyConnectedSpace_sphere (by omega)
  have : SimplyConnectedSpace M := e.simplyConnectedSpace
  exact ⟨simplyConnectedSpace_compl_chartDisk hn hd,
    SingularPair.acyclic_compl_image_diskInterior_Z (by omega) e hd⟩

end PoincareHighDim
