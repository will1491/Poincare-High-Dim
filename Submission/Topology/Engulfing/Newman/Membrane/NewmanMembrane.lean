/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Topology.Disks.DiskExtension
import Submission.Topology.Disks.TwistedSphere
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Continuous membranes for a single attachment

Newman's membrane construction first fills the boundary of an attaching disk inside
the current open cell, then fills the resulting sphere in the ambient space. The
lower hemisphere agrees exactly with the original attachment; the upper hemisphere
maps into the cell. No embedding assertion is imposed on the membrane interior.
-/

namespace PoincareHighDim.Engulfing

open Set Metric Topology
open scoped ContinuousMap

variable {M : Type*} [TopologicalSpace M]

/-- Include the unit sphere as the boundary of the unit disk. -/
def sphereToDisk (q : ℕ) : C(sphere (0 : EuclideanSpace ℝ (Fin q)) 1, Disk q) where
  toFun x := ⟨x.1, sphere_subset_closedBall x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The lower disk in the boundary of the membrane disk. -/
noncomputable def membraneBase (k : ℕ) : C(Disk (k + 1), Disk (k + 2)) :=
  (sphereToDisk (k + 2)).comp ⟨lowerHemisphere k, continuous_lowerHemisphere k⟩

/-- The upper disk in the boundary of the membrane disk. -/
noncomputable def membraneRoof (k : ℕ) : C(Disk (k + 1), Disk (k + 2)) :=
  (sphereToDisk (k + 2)).comp ⟨upperHemisphere k, continuous_upperHemisphere k⟩

theorem membraneBase_injective (k : ℕ) : Function.Injective (membraneBase k) := by
  intro x y hxy
  apply lowerHemisphere_injective k
  exact Subtype.ext (congrArg (fun z : Disk (k + 2) => z.1) hxy)

theorem membraneRoof_injective (k : ℕ) : Function.Injective (membraneRoof k) := by
  intro x y hxy
  apply upperHemisphere_injective k
  exact Subtype.ext (congrArg (fun z : Disk (k + 2) => z.1) hxy)

theorem membraneBase_isClosedEmbedding (k : ℕ) : IsClosedEmbedding (membraneBase k) :=
  (membraneBase k).continuous.isClosedEmbedding (membraneBase_injective k)

theorem membraneRoof_isClosedEmbedding (k : ℕ) : IsClosedEmbedding (membraneRoof k) :=
  (membraneRoof k).continuous.isClosedEmbedding (membraneRoof_injective k)

/-- The two parameterized faces cover exactly the boundary of the membrane. -/
theorem range_membraneBase_union_range_membraneRoof (k : ℕ) :
    range (membraneBase k) ∪ range (membraneRoof k) = diskSphere (k + 2) := by
  ext x
  constructor
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact (lowerHemisphere k y).2
    · exact (upperHemisphere k y).2
  · intro hx
    let s : sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 := ⟨x.1, hx⟩
    have hs : s ∈ range (lowerHemisphere k) ∪ range (upperHemisphere k) :=
      (range_lowerHemisphere_union_range_upperHemisphere k).symm ▸ mem_univ s
    rcases hs with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨y, Subtype.ext (congrArg
        (fun z : sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 => z.1) hy)⟩
    · exact Or.inr ⟨y, Subtype.ext (congrArg
        (fun z : sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1 => z.1) hy)⟩

theorem membraneBase_eq_membraneRoof_iff (k : ℕ) (x y : Disk (k + 1)) :
    membraneBase k x = membraneRoof k y ↔ x = y ∧ x ∈ diskSphere (k + 1) := by
  change (sphereToDisk (k + 2)) (lowerHemisphere k x) =
    (sphereToDisk (k + 2)) (upperHemisphere k y) ↔ _
  have hinj : Function.Injective (sphereToDisk (k + 2)) :=
    fun _ _ h => Subtype.ext (congrArg (fun z : Disk (k + 2) => z.1) h)
  rw [hinj.eq_iff]
  exact lowerHemisphere_eq_upperHemisphere_iff k x y

theorem membraneBase_mem_range_membraneRoof_iff (k : ℕ) (x : Disk (k + 1)) :
    membraneBase k x ∈ range (membraneRoof k) ↔ x ∈ diskSphere (k + 1) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ((membraneBase_eq_membraneRoof_iff k x y).mp hy.symm).2
  · intro hx
    exact ⟨x, ((membraneBase_eq_membraneRoof_iff k x x).mpr ⟨rfl, hx⟩).symm⟩

/-- Gluing two disk maps agreeing on the boundary gives a sphere map, with exact
formulas on both hemisphere parametrizations. -/
theorem exists_sphere_map_of_disk_pair {k : ℕ} (f g : C(Disk (k + 1), M))
    (hboundary : ∀ x ∈ diskSphere (k + 1), f x = g x) :
    ∃ b : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1, M),
      (∀ x, b (lowerHemisphere k x) = f x) ∧
      (∀ x, b (upperHemisphere k x) = g x) := by
  let q : C(Disk (k + 1) ⊕ Disk (k + 1),
      sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
    ⟨Sum.elim (lowerHemisphere k) (upperHemisphere k),
      (continuous_lowerHemisphere k).sumElim (continuous_upperHemisphere k)⟩
  have hqsurj : Function.Surjective q := by
    intro x
    have hx : x ∈ range (lowerHemisphere k) ∪ range (upperHemisphere k) :=
      (range_lowerHemisphere_union_range_upperHemisphere k).symm ▸ mem_univ x
    rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨Sum.inl y, rfl⟩
    · exact ⟨Sum.inr y, rfl⟩
  have hq : IsQuotientMap q := .of_surjective_continuous hqsurj q.continuous
  let a : C(Disk (k + 1) ⊕ Disk (k + 1), M) :=
    ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩
  have ha : Function.FactorsThrough a q := by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg f (lowerHemisphere_injective k hxy)
    · obtain ⟨rfl, hx⟩ := (lowerHemisphere_eq_upperHemisphere_iff k x y).mp hxy
      exact hboundary x hx
    · obtain ⟨rfl, hx⟩ := (lowerHemisphere_eq_upperHemisphere_iff k y x).mp hxy.symm
      exact (hboundary y hx).symm
    · exact congrArg g (upperHemisphere_injective k hxy)
  let b := hq.lift a ha
  have hb := hq.lift_comp a ha
  refine ⟨b, fun x => ?_, fun x => ?_⟩
  · exact congrArg (fun c => c (Sum.inl x)) hb
  · exact congrArg (fun c => c (Sum.inr x)) hb

/-- A continuous membrane has the prescribed attaching disk as its lower face and
has its remaining boundary in the engulfing set. -/
structure DiskMembrane {k : ℕ} (f : C(Disk (k + 1), M)) (U : Set M) where
  map : C(Disk (k + 2), M)
  base_eq : ∀ x, map (membraneBase k x) = f x
  roof_mem : ∀ x, map (membraneRoof k x) ∈ U

namespace DiskMembrane

variable {k : ℕ} {f : C(Disk (k + 1), M)} {U : Set M} (m : DiskMembrane f U)

/-- Every boundary point outside the attaching face maps into the current cell. -/
theorem boundary_mem_of_not_mem_base {x : Disk (k + 2)}
    (hx : x ∈ diskSphere (k + 2)) (hxbase : x ∉ range (membraneBase k)) : m.map x ∈ U := by
  have hx' : x ∈ range (membraneBase k) ∪ range (membraneRoof k) :=
    (range_membraneBase_union_range_membraneRoof k).symm ▸ hx
  obtain ⟨y, rfl⟩ := hx'.resolve_left hxbase
  exact m.roof_mem y

/-- Every prescribed subset of the attaching disk keeps its original image. -/
theorem image_base (A : Set (Disk (k + 1))) :
    m.map '' (membraneBase k '' A) = f '' A := by
  rw [image_image]
  congr 1
  funext x
  exact m.base_eq x

/-- In particular a fixed embedded subcomplex on the attaching face remains embedded. -/
theorem isEmbedding_base_restrict {A : Set (Disk (k + 1))}
    (hf : IsEmbedding (fun x : A => f x.1)) :
    IsEmbedding (fun x : A => m.map (membraneBase k x.1)) := by
  simpa only [m.base_eq] using hf

end DiskMembrane

/-- The two connectivity inputs in the membrane argument, separated from geometry. -/
theorem exists_diskMembrane_of_nullhomotopic
    {k : ℕ} (f : C(Disk (k + 1), M)) (U : Set M)
    (hboundary : ∀ x ∈ diskSphere (k + 1), f x ∈ U)
    (hU : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, U), b.Nullhomotopic)
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1, M), b.Nullhomotopic) :
    Nonempty (DiskMembrane f U) := by
  let a : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, U) :=
    ⟨fun x => ⟨f ((diskSphereHomeomorph (k + 1)).symm x).1,
        hboundary _ ((diskSphereHomeomorph (k + 1)).symm x).2⟩,
      (f.continuous.comp (continuous_subtype_val.comp
        (diskSphereHomeomorph (k + 1)).symm.continuous)).subtype_mk _⟩
  obtain ⟨g, hg⟩ := exists_disk_extension_of_nullhomotopic a (hU a)
  let gM : C(Disk (k + 1), M) := ⟨fun x => g x, continuous_subtype_val.comp g.continuous⟩
  have hfg : ∀ x ∈ diskSphere (k + 1), f x = gM x := by
    intro x hx
    have h := congrArg Subtype.val (hg ⟨x, hx⟩)
    simpa only [a, gM, ContinuousMap.coe_mk, Homeomorph.symm_apply_apply] using h.symm
  obtain ⟨b, hb₀, hb₁⟩ := exists_sphere_map_of_disk_pair f gM hfg
  obtain ⟨F, hF⟩ := exists_disk_extension_of_nullhomotopic b (hM b)
  have hext (x : sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :
      F (sphereToDisk (k + 2) x) = b x := by
    exact hF ⟨sphereToDisk (k + 2) x, x.2⟩
  refine ⟨⟨F, fun x => (hext (lowerHemisphere k x)).trans (hb₀ x), ?_⟩⟩
  intro x
  change F (sphereToDisk (k + 2) (upperHemisphere k x)) ∈ U
  rw [hext, hb₁]
  exact (g x).2

/-- An equivalent membrane interface stated directly with disk-extension hypotheses.
The subset `U` is arbitrary; it can in particular be an annulus or a chart complement. -/
theorem exists_diskMembrane_of_sphere_extensions {k : ℕ}
    (f : C(Disk (k + 1), M)) (U : Set M)
    (hboundary : ∀ x ∈ diskSphere (k + 1), f x ∈ U)
    (hU : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, U),
      ∃ F : C(Disk (k + 1), U), ∀ x : diskSphere (k + 1),
        F x.1 = b (diskSphereHomeomorph (k + 1) x))
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1, M),
      ∃ F : C(Disk (k + 2), M), ∀ x : diskSphere (k + 2),
        F x.1 = b (diskSphereHomeomorph (k + 2) x)) :
    Nonempty (DiskMembrane f U) := by
  apply exists_diskMembrane_of_nullhomotopic f U hboundary
  · intro b
    obtain ⟨F, hF⟩ := hU b
    exact nullhomotopic_of_disk_extension b F hF
  · intro b
    obtain ⟨F, hF⟩ := hM b
    exact nullhomotopic_of_disk_extension b F hF

/-- An open Euclidean cell supplies the lower-dimensional connectivity input. -/
theorem exists_diskMembrane_in_open_cell {k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : E → M} (hj : IsOpenEmbedding j)
    (f : C(Disk (k + 1), M))
    (hboundary : ∀ x ∈ diskSphere (k + 1), f x ∈ range j)
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1, M), b.Nullhomotopic) :
    Nonempty (DiskMembrane f (range j)) := by
  let : ContractibleSpace (range j) := hj.isEmbedding.toHomeomorph.symm.contractibleSpace
  exact exists_diskMembrane_of_nullhomotopic f (range j) hboundary
    (fun b => (id_nullhomotopic (range j)).comp_left b) hM

/-- The construction works in the current cell after any ambient homeomorphism. -/
theorem exists_diskMembrane_in_moved_cell {k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : E → M} (hj : IsOpenEmbedding j) (H : M ≃ₜ M)
    (f : C(Disk (k + 1), M))
    (hboundary : ∀ x ∈ diskSphere (k + 1), f x ∈ H '' range j)
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1, M), b.Nullhomotopic) :
    Nonempty (DiskMembrane f (H '' range j)) := by
  simpa only [range_comp] using exists_diskMembrane_in_open_cell
    (H.isOpenEmbedding.comp hj) f (by simpa only [range_comp] using hboundary) hM

/-- Homotopy spheres provide the ambient connectivity required for a membrane. -/
theorem exists_diskMembrane_of_homotopyEquiv_sphere {k n : ℕ} (hkn : k + 3 ≤ n)
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : E → M} (hj : IsOpenEmbedding j) (f : C(Disk (k + 1), M))
    (hboundary : ∀ x ∈ diskSphere (k + 1), f x ∈ range j) :
    Nonempty (DiskMembrane f (range j)) :=
  exists_diskMembrane_in_open_cell hj f hboundary
    (fun b => nullhomotopic_map_of_homotopyEquiv_sphere hkn e b)

/-- The zero-dimensional attachment starts with a path from its point into the cell. -/
theorem exists_point_membrane [PathConnectedSpace M] {E : Type*} [Zero E]
    (j : E → M) (x : M) : ∃ y ∈ range j, Nonempty (Path x y) :=
  ⟨j 0, mem_range_self 0, PathConnectedSpace.joined x (j 0)⟩

/-- A compact convex body has a disk parametrization carrying its boundary exactly
to the sphere. This will be applied to the attaching simplex. -/
theorem exists_disk_homeomorph_convex_body {q : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin q))} (hC : IsCompact C) (hconv : Convex ℝ C)
    (hint : (interior C).Nonempty) :
    ∃ e : Disk q ≃ₜ C, ∀ x, x ∈ diskSphere q ↔ (e x).1 ∈ frontier C := by
  obtain ⟨h, -, hclosed, hfront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hint hC.isBounded
  rw [hC.isClosed.closure_eq] at hclosed
  let d : C ≃ₜ Disk q := (h.image C).trans (Homeomorph.setCongr hclosed)
  have hd (z : C) : (d z).1 = h z.1 := rfl
  refine ⟨d.symm, fun x => ?_⟩
  have hx : h (d.symm x).1 = x.1 := by
    rw [← hd]
    exact congrArg (fun z : Disk q => z.1) (d.apply_symm_apply x)
  constructor
  · intro hxs
    have hmem : h (d.symm x).1 ∈ h '' frontier C := by
      rw [hfront, hx]
      exact hxs
    exact h.injective.mem_set_image.mp hmem
  · intro hf
    have hmem : h (d.symm x).1 ∈ sphere (0 : EuclideanSpace ℝ (Fin q)) 1 :=
      hfront ▸ mem_image_of_mem h hf
    rwa [hx] at hmem

/-- A simplex, or any full-dimensional compact convex body, can be used as the exact
attaching face of a disk membrane. The other face maps into the current open cell. -/
theorem exists_convex_body_membrane {k : ℕ} {C : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hC : IsCompact C) (hconv : Convex ℝ C) (hint : (interior C).Nonempty)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : E → M} (hj : IsOpenEmbedding j) (f : C(C, M))
    (hboundary : ∀ x : C, x.1 ∈ frontier C → f x ∈ range j)
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1, M), b.Nullhomotopic) :
    ∃ a : C(C, Disk (k + 2)), IsClosedEmbedding a ∧
      ∃ F : C(Disk (k + 2), M), (∀ x, F (a x) = f x) ∧
        (∀ x ∈ diskSphere (k + 2), x ∉ range a → F x ∈ range j) ∧
        (∀ x : C, x.1 ∈ frontier C ↔ a x ∈ range (membraneRoof k)) := by
  obtain ⟨e, he⟩ := exists_disk_homeomorph_convex_body hC hconv hint
  obtain ⟨m⟩ := exists_diskMembrane_in_open_cell hj (f.comp ⟨e, e.continuous⟩)
    (fun x hx => hboundary (e x) ((he x).mp hx)) hM
  let a : C(C, Disk (k + 2)) := (membraneBase k).comp ⟨e.symm, e.symm.continuous⟩
  have ha : IsClosedEmbedding a :=
    (membraneBase_isClosedEmbedding k).comp e.symm.isClosedEmbedding
  have hrange : range a = range (membraneBase k) := by
    change range (membraneBase k ∘ e.symm) = _
    rw [range_comp, e.symm.surjective.range_eq, image_univ]
  refine ⟨a, ha, m.map, fun x => ?_, ?_, fun x => ?_⟩
  · exact (m.base_eq (e.symm x)).trans (congrArg f (e.apply_symm_apply x))
  · intro x hx hxa
    exact m.boundary_mem_of_not_mem_base hx (hrange ▸ hxa)
  · change x.1 ∈ frontier C ↔ membraneBase k (e.symm x) ∈ range (membraneRoof k)
    rw [membraneBase_mem_range_membraneRoof_iff, he, e.apply_symm_apply]

/-- The convex-body attachment theorem with both connectivity assumptions explicit.
In particular the roof target need not itself be an open cell. -/
theorem exists_convex_body_membrane_of_nullhomotopic
    {k : ℕ} {C : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hC : IsCompact C) (hconv : Convex ℝ C) (hint : (interior C).Nonempty)
    (U : Set M) (f : C(C, M))
    (hboundary : ∀ x : C, x.1 ∈ frontier C → f x ∈ U)
    (hU : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, U), b.Nullhomotopic)
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1, M), b.Nullhomotopic) :
    ∃ a : C(C, Disk (k + 2)), IsClosedEmbedding a ∧
      ∃ F : C(Disk (k + 2), M), (∀ x, F (a x) = f x) ∧
        (∀ x ∈ diskSphere (k + 2), x ∉ range a → F x ∈ U) ∧
        (∀ x : C, x.1 ∈ frontier C ↔ a x ∈ range (membraneRoof k)) := by
  obtain ⟨e, he⟩ := exists_disk_homeomorph_convex_body hC hconv hint
  obtain ⟨m⟩ := exists_diskMembrane_of_nullhomotopic (f.comp ⟨e, e.continuous⟩) U
    (fun x hx => hboundary (e x) ((he x).mp hx)) hU hM
  let a : C(C, Disk (k + 2)) := (membraneBase k).comp ⟨e.symm, e.symm.continuous⟩
  have ha : IsClosedEmbedding a :=
    (membraneBase_isClosedEmbedding k).comp e.symm.isClosedEmbedding
  have hrange : range a = range (membraneBase k) := by
    change range (membraneBase k ∘ e.symm) = _
    rw [range_comp, e.symm.surjective.range_eq, image_univ]
  refine ⟨a, ha, m.map, fun x => ?_, ?_, fun x => ?_⟩
  · exact (m.base_eq (e.symm x)).trans (congrArg f (e.apply_symm_apply x))
  · intro x hx hxa
    exact m.boundary_mem_of_not_mem_base hx (hrange ▸ hxa)
  · change x.1 ∈ frontier C ↔ membraneBase k (e.symm x) ∈ range (membraneRoof k)
    rw [membraneBase_mem_range_membraneRoof_iff, he, e.apply_symm_apply]

/-- In particular, the boundary-controlled map of a finite full simplex is the
attaching face of a membrane. -/
theorem exists_affineBasis_membrane {k : ℕ}
    (v : AffineBasis (Fin (k + 2)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : E → M} (hj : IsOpenEmbedding j)
    (f : C(convexHull ℝ (range v), M))
    (hboundary : ∀ x : convexHull ℝ (range v),
      x.1 ∈ frontier (convexHull ℝ (range v)) → f x ∈ range j)
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1, M), b.Nullhomotopic) :
    ∃ a : C(convexHull ℝ (range v), Disk (k + 2)), IsClosedEmbedding a ∧
      ∃ F : C(Disk (k + 2), M), (∀ x, F (a x) = f x) ∧
        (∀ x ∈ diskSphere (k + 2), x ∉ range a → F x ∈ range j) ∧
        (∀ x : convexHull ℝ (range v), x.1 ∈ frontier (convexHull ℝ (range v)) ↔
          a x ∈ range (membraneRoof k)) :=
  exists_convex_body_membrane ((finite_range v).isCompact_convexHull ℝ)
    (convex_convexHull ℝ _) ⟨_, v.centroid_mem_interior_convexHull⟩ hj f hboundary hM

end PoincareHighDim.Engulfing
