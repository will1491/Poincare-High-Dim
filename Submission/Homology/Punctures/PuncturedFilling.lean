import Submission.Homology.Punctures.DiskExcision
import Submission.Homology.Punctures.PuncturedAcyclic

/-!
# Removing a chart disk from an acyclic filling

If a subset `B` of a manifold contains a closed chart disk `D`, then excision and a radial
deformation identify `H_*(B \ int D, ∂D)` with `H_*(B, D)`. Consequently, if `B` is acyclic,
the punctured filling has vanishing homology relative to the boundary of the removed disk.

The filling need not be contractible, open, or itself a manifold. Containment of the closed
chart disk supplies the neighborhood needed for excision.
-/

open CategoryTheory Limits Set

noncomputable section

universe u

namespace PoincareHighDim

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {e : Disk n → M} {B : Set M}

/-- Shrinking the deleted open disk to its closed half disk does not change the homotopy type
of the complement within any subset containing the whole closed disk. -/
theorem IsChartDisk.isHomotopyEquivInclusion_sdiff_halfDisk (he : IsChartDisk e)
    (hD : range e ⊆ B) :
    IsHomotopyEquivInclusion (B \ e '' diskInterior n) (B \ e '' halfDisk n) := by
  have h := he.isHomotopyEquivInclusion_annulus (ρ := 1 / 2) (by norm_num)
    (B := B \ e '' halfDisk n) ?_ ?_
  · convert h using 1
    ext x
    constructor
    · rintro ⟨hxB, hxU⟩
      refine ⟨⟨hxB, fun hK => hxU (image_halfDisk_subset_image_diskInterior e hK)⟩, ?_⟩
      rintro ⟨v, hv, rfl⟩
      exact hxU ⟨v, mem_diskInterior.2 hv.2, rfl⟩
    · rintro ⟨⟨hxB, hxK⟩, hxAnn⟩
      refine ⟨hxB, ?_⟩
      rintro ⟨v, hv, rfl⟩
      rw [mem_diskInterior] at hv
      by_cases h : ‖(v : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2
      · exact hxK ⟨v, h, rfl⟩
      · exact hxAnn ⟨v, ⟨not_le.1 h, hv⟩, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨hD (mem_range_self v), ?_⟩
    intro h
    rw [he.injective.mem_set_image, mem_halfDisk] at h
    exact absurd hv (not_lt.2 h)
  · exact disjoint_sdiff_left

namespace SingularPair

variable (R : ModuleCat.{u} ℤ)

/-- Removing an open chart disk from a subset containing it identifies relative homology at
the new sphere boundary with relative homology of the original subset modulo the disk. -/
def HrelPuncturedFillingIso (he : IsChartDisk e) (hD : range e ⊆ B) (k : ℕ) :
    Hrel R (TopCat.of (B \ e '' diskInterior n : Set M)) (Subtype.val ⁻¹' (e '' diskSphere n)) k ≅
      Hrel R (TopCat.of B) (Subtype.val ⁻¹' (range e)) k := by
  have hS : e '' diskSphere n ⊆ B \ e '' diskInterior n := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨hD (mem_range_self v), ?_⟩
    intro h
    rw [he.injective.mem_set_image] at h
    exact Set.disjoint_left.1 (disjoint_diskSphere_diskInterior n) hv h
  have hcollar : range e \ e '' halfDisk n ⊆ B \ e '' halfDisk n := by
    rintro x ⟨hxD, hxK⟩
    exact ⟨hD hxD, hxK⟩
  have hsub : B \ e '' diskInterior n ⊆ B \ e '' halfDisk n :=
    sdiff_subset_sdiff_right (image_halfDisk_subset_image_diskInterior e)
  have hpair : (Subtype.val ⁻¹' (range e \ e '' halfDisk n) :
      Set (B \ e '' halfDisk n : Set M)) = Subtype.val ⁻¹' (range e) := by
    ext ⟨x, hx⟩
    exact and_iff_left hx.2
  have hset : (Subtype.val ⁻¹' (B \ e '' halfDisk n) : Set B) =
      (Subtype.val ⁻¹' (e '' halfDisk n))ᶜ := by
    ext ⟨x, hx⟩
    exact and_iff_right hx
  have hexc : closure (Subtype.val ⁻¹' (e '' halfDisk n) : Set B) ⊆
      interior (Subtype.val ⁻¹' (range e)) := by
    rw [(he.isClosed_image_halfDisk.preimage continuous_subtype_val).closure_eq]
    exact (preimage_mono (image_halfDisk_subset_image_diskInterior e)).trans
      (interior_maximal (preimage_mono (image_subset_range _ _))
        (he.isOpen_image_diskInterior.preimage continuous_subtype_val))
  let φ₁ :
      Hrel R (TopCat.of (B \ e '' diskInterior n : Set M))
          (Subtype.val ⁻¹' (e '' diskSphere n)) k ≅
        Hrel R (TopCat.of (B \ e '' halfDisk n : Set M))
          (Subtype.val ⁻¹' (range e \ e '' halfDisk n)) k :=
    HrelIsoOfHomotopyEquivInclusion R hS hcollar hsub
      (image_diskSphere_subset_range_sdiff_halfDisk he)
      (he.isHomotopyEquivInclusion_sdiff_halfDisk hD)
      he.isHomotopyEquivInclusion_image_diskSphere k
  let φ₂ :
      Hrel R (TopCat.of (B \ e '' halfDisk n : Set M))
          (Subtype.val ⁻¹' (range e \ e '' halfDisk n)) k ≅
        Hrel R (TopCat.of (B \ e '' halfDisk n : Set M))
          (Subtype.val ⁻¹' (range e)) k :=
    HrelIsoOfEq R _ hpair k
  let φ₃ :
      Hrel R (TopCat.of (B \ e '' halfDisk n : Set M))
          (Subtype.val ⁻¹' (range e)) k ≅
        Hrel R (TopCat.of (Subtype.val ⁻¹' (B \ e '' halfDisk n) : Set B))
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e))) k :=
    (HrelIsoOfSubtypeSubtype R (show B \ e '' halfDisk n ⊆ B from sdiff_subset)
      (range e) k).symm
  let φ₄ :
      Hrel R (TopCat.of (Subtype.val ⁻¹' (B \ e '' halfDisk n) : Set B))
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e))) k ≅
        Hrel R (TopCat.of ((Subtype.val ⁻¹' (e '' halfDisk n))ᶜ : Set B))
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e))) k :=
    HrelIsoOfHomeomorphIff R
      (Homeomorph.setCongr
        (s := (Subtype.val ⁻¹' (B \ e '' halfDisk n) : Set B))
        (t := ((Subtype.val ⁻¹' (e '' halfDisk n))ᶜ : Set B)) hset)
      (A := Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e)))
      (B := Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e)))
      (fun _ => by exact Iff.rfl) k
  let φ₅ :
      Hrel R (TopCat.of ((Subtype.val ⁻¹' (e '' halfDisk n))ᶜ : Set B))
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e))) k ≅
        Hrel R (TopCat.of B) (Subtype.val ⁻¹' (range e)) k :=
    excisionClosedIso R (X := TopCat.of B) (Subtype.val ⁻¹' (e '' halfDisk n))
      (Subtype.val ⁻¹' (range e)) hexc k
  exact φ₁ ≪≫ φ₂ ≪≫ φ₃ ≪≫ φ₄ ≪≫ φ₅

/-- The puncture of an acyclic filling has zero homology relative to the newly created sphere
boundary. Coefficients are arbitrary. -/
theorem isZero_Hrel_puncturedFilling (he : IsChartDisk e) (hD : range e ⊆ B)
    (hB : Acyclic R (TopCat.of B)) (k : ℕ) :
    IsZero (Hrel R (TopCat.of (B \ e '' diskInterior n : Set M))
      (Subtype.val ⁻¹' (e '' diskSphere n)) k) := by
  have : ContractibleSpace (Subtype.val ⁻¹' (range e) : Set B) := by
    have := he.contractibleSpace_range
    exact (homeomorphPreimageVal hD).contractibleSpace
  exact (isZero_Hrel_of_contractible_of_acyclic' R hB k).of_iso
    (HrelPuncturedFillingIso R he hD k)

/-- Integral homology of a punctured acyclic filling vanishes relative to the boundary sphere
of the removed chart disk, as required by the h-cobordism theorem. -/
theorem relHomologyVanishes_puncturedFilling (he : IsChartDisk e) (hD : range e ⊆ B)
    (hB : Acyclic Z.{u} (TopCat.of B)) :
    RelHomologyVanishes (B \ e '' diskInterior n : Set M) (Subtype.val ⁻¹' (e '' diskSphere n)) :=
  isZero_Hrel_puncturedFilling Z he hD hB

end SingularPair

end PoincareHighDim

end
