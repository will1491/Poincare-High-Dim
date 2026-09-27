import Submission.Homology.Punctures.ChartDiskRetract
import Submission.Homology.Relative.RelHomotopy
import Submission.Homology.Relative.DeltaIso

/-!
# Excising the first chart disk from the strip

Let `e₀, e₁ : Disk n → M` be two chart disks with disjoint ranges in a Hausdorff space `M`,
with open disks `U_i := e_i '' diskInterior n`, closed disk `D₀ := range e₀`, boundary sphere
`S₀ := e₀ '' diskSphere n` and half disk `H₀ := e₀ '' halfDisk n`.  The strip
`W := (U₀ ∪ U₁)ᶜ` with its first boundary sphere `S₀` has the same relative homology as the pair
`(M ∖ U₁, D₀)`:

`H_k(W, S₀) ≅ H_k(M ∖ U₁, D₀)` (`HrelWIso`).

The isomorphism is the composite of

* relative homotopy invariance (`HrelIsoOfHomotopyEquivInclusion`) for the inclusion of pairs
  `(W, S₀) ↪ (W', D₀ ∖ H₀)`, `W' := (H₀ ∪ U₁)ᶜ`, both members being deformation retractions
  (`isHomotopyEquivInclusion_compl_halfDisk_union`,
  `IsChartDisk.isHomotopyEquivInclusion_image_diskSphere` of
  `Submission.Homology.Punctures.ChartDiskRetract`);
* the identification of the pair `(W', D₀ ∖ H₀)` with the pair `(X ∖ H₀, D₀ ∖ H₀)` inside
  `X := M ∖ U₁` (`HrelIsoOfEq`, `HrelIsoOfSubtypeSubtype`, `HrelIsoOfHomeomorphIff`);
* excision of the closed set `H₀ ⊆ interior D₀` from the pair `(X, D₀)` (`excisionClosedIso`).
-/

open CategoryTheory Limits Set

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

section chartDisks

variable {n : ℕ} {M : Type u}

/-! ### Set-theoretic bookkeeping -/

section sets

variable {e₀ e₁ : Disk n → M}

/-- The collar `D₀ ∖ H₀` lies in the enlarged strip `(H₀ ∪ U₁)ᶜ`. -/
theorem range_sdiff_halfDisk_subset_compl_union (hdisj : Disjoint (range e₀) (range e₁)) :
    range e₀ \ e₀ '' halfDisk n ⊆ (e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ := by
  rintro x ⟨hx, hH⟩ (h | h)
  · exact hH h
  · exact Set.disjoint_left.1 hdisj hx (image_subset_range _ _ h)

/-- The strip lies in the enlarged strip. -/
theorem compl_union_subset_compl_halfDisk_union :
    (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ ⊆
      (e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ :=
  compl_subset_compl.2 (union_subset_union_left _ (image_halfDisk_subset_image_diskInterior e₀))

/-- The enlarged strip lies in the complement of the second open disk. -/
theorem compl_halfDisk_union_subset_compl :
    (e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ ⊆ (e₁ '' diskInterior n)ᶜ :=
  compl_subset_compl.2 subset_union_right

/-- Inside the enlarged strip, the collar `D₀ ∖ H₀` is just `D₀`. -/
theorem preimage_val_range_sdiff_halfDisk :
    (Subtype.val ⁻¹' (range e₀ \ e₀ '' halfDisk n) :
        Set ((e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ : Set M)) =
      Subtype.val ⁻¹' (range e₀) := by
  ext ⟨x, hx⟩
  simp only [mem_preimage, mem_sdiff, and_iff_left_iff_imp]
  intro _ h
  exact hx (Or.inl h)

/-- Inside `M ∖ U₁`, the complement of `H₀` is the enlarged strip. -/
theorem compl_preimage_val_halfDisk_eq :
    ((Subtype.val ⁻¹' (e₀ '' halfDisk n))ᶜ : Set ((e₁ '' diskInterior n)ᶜ : Set M)) =
      Subtype.val ⁻¹' (e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ := by
  ext ⟨x, hx⟩
  simp only [mem_compl_iff, mem_preimage, mem_union, not_or]
  exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩

end sets

section topology

variable [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e₀ e₁ : Disk n → M}

omit [T2Space M] in
/-- The first boundary sphere lies in the strip. -/
theorem image_diskSphere_subset_compl_union (h₀ : IsChartDisk e₀)
    (hdisj : Disjoint (range e₀) (range e₁)) :
    e₀ '' diskSphere n ⊆ (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ := by
  rintro _ ⟨v, hv, rfl⟩ (h | h)
  · rw [h₀.injective.mem_set_image] at h
    exact Set.disjoint_left.1 (disjoint_diskSphere_diskInterior n) hv h
  · exact Set.disjoint_left.1 hdisj (mem_range_self v) (image_subset_range _ _ h)

omit [T2Space M] in
/-- The boundary sphere lies in the collar. -/
theorem image_diskSphere_subset_range_sdiff_halfDisk (h₀ : IsChartDisk e₀) :
    e₀ '' diskSphere n ⊆ range e₀ \ e₀ '' halfDisk n := by
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨mem_range_self v, fun h => ?_⟩
  rw [h₀.injective.mem_set_image, mem_halfDisk] at h
  rw [mem_diskSphere] at hv
  linarith

/-- Inside `M ∖ U₁`, the half disk `H₀` is closed and contained in the interior of `D₀`. -/
theorem closure_preimage_val_halfDisk_subset (h₀ : IsChartDisk e₀) :
    closure (Subtype.val ⁻¹' (e₀ '' halfDisk n) : Set ((e₁ '' diskInterior n)ᶜ : Set M)) ⊆
      interior (Subtype.val ⁻¹' (range e₀)) := by
  rw [(h₀.isClosed_image_halfDisk.preimage continuous_subtype_val).closure_eq]
  exact (preimage_mono (image_halfDisk_subset_image_diskInterior e₀)).trans
    (interior_maximal (preimage_mono (image_subset_range _ _))
      (h₀.isOpen_image_diskInterior.preimage continuous_subtype_val))

/-! ### The isomorphism, piece by piece -/

/-- Step 1: relative homotopy invariance, `H_k(W, S₀) ≅ H_k(W', D₀ ∖ H₀)`. -/
def HrelWIso₁ (h₀ : IsChartDisk e₀) (hdisj : Disjoint (range e₀) (range e₁)) (k : ℕ) :
    Hrel R (TopCat.of ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M))
        (Subtype.val ⁻¹' (e₀ '' diskSphere n)) k ≅
      Hrel R (TopCat.of ((e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ : Set M))
        (Subtype.val ⁻¹' (range e₀ \ e₀ '' halfDisk n)) k :=
  HrelIsoOfHomotopyEquivInclusion R (image_diskSphere_subset_compl_union h₀ hdisj)
    (range_sdiff_halfDisk_subset_compl_union hdisj) compl_union_subset_compl_halfDisk_union
    (image_diskSphere_subset_range_sdiff_halfDisk h₀)
    (isHomotopyEquivInclusion_compl_halfDisk_union h₀ hdisj)
    h₀.isHomotopyEquivInclusion_image_diskSphere k

omit [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] in
/-- Step 2: `H_k(W', D₀ ∖ H₀) ≅ H_k(W', D₀)`. -/
def HrelWIso₂ (k : ℕ) :
    Hrel R (TopCat.of ((e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ : Set M))
        (Subtype.val ⁻¹' (range e₀ \ e₀ '' halfDisk n)) k ≅
      Hrel R (TopCat.of ((e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ : Set M))
        (Subtype.val ⁻¹' (range e₀)) k :=
  HrelIsoOfEq R _ preimage_val_range_sdiff_halfDisk k

omit [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] in
/-- Step 3: `H_k(W', D₀) ≅ H_k(X ∖ H₀, D₀ ∖ H₀)` inside `X := M ∖ U₁`. -/
def HrelWIso₃ (k : ℕ) :
    Hrel R (TopCat.of ((e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ : Set M))
        (Subtype.val ⁻¹' (range e₀)) k ≅
      Hrel R (TopCat.of ((Subtype.val ⁻¹' (e₀ '' halfDisk n))ᶜ :
          Set ((e₁ '' diskInterior n)ᶜ : Set M)))
        (Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e₀))) k :=
  (HrelIsoOfSubtypeSubtype R compl_halfDisk_union_subset_compl (range e₀) k).symm ≪≫
    HrelIsoOfHomeomorphIff R
      (Homeomorph.setCongr
        (s := (Subtype.val ⁻¹' (e₀ '' halfDisk n ∪ e₁ '' diskInterior n)ᶜ :
          Set ((e₁ '' diskInterior n)ᶜ : Set M)))
        (t := ((Subtype.val ⁻¹' (e₀ '' halfDisk n))ᶜ : Set ((e₁ '' diskInterior n)ᶜ : Set M)))
        compl_preimage_val_halfDisk_eq.symm)
      (fun _ => by exact Iff.rfl) k

/-- Step 4: excision, `H_k(X ∖ H₀, D₀ ∖ H₀) ≅ H_k(X, D₀)`. -/
def HrelWIso₄ (h₀ : IsChartDisk e₀) (k : ℕ) :
    Hrel R (TopCat.of ((Subtype.val ⁻¹' (e₀ '' halfDisk n))ᶜ :
          Set ((e₁ '' diskInterior n)ᶜ : Set M)))
        (Subtype.val ⁻¹' (Subtype.val ⁻¹' (range e₀))) k ≅
      Hrel R (TopCat.of ((e₁ '' diskInterior n)ᶜ : Set M)) (Subtype.val ⁻¹' (range e₀)) k :=
  excisionClosedIso R (X := TopCat.of ((e₁ '' diskInterior n)ᶜ : Set M))
    (Subtype.val ⁻¹' (e₀ '' halfDisk n)) (Subtype.val ⁻¹' (range e₀))
    (closure_preimage_val_halfDisk_subset h₀) k

/-- **Excising the first disk.**  `H_k(W, S₀) ≅ H_k(M ∖ U₁, D₀)`, where `W = (U₀ ∪ U₁)ᶜ` is the
strip between two chart disks with disjoint ranges, `S₀` its first boundary sphere and
`D₀ = range e₀` the first closed disk. -/
def HrelWIso (h₀ : IsChartDisk e₀) (hdisj : Disjoint (range e₀) (range e₁)) (k : ℕ) :
    Hrel R (TopCat.of ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M))
        (Subtype.val ⁻¹' (e₀ '' diskSphere n)) k ≅
      Hrel R (TopCat.of ((e₁ '' diskInterior n)ᶜ : Set M)) (Subtype.val ⁻¹' (range e₀)) k :=
  HrelWIso₁ R h₀ hdisj k ≪≫ HrelWIso₂ R k ≪≫ HrelWIso₃ R k ≪≫ HrelWIso₄ R h₀ k

end topology

end chartDisks

end PoincareHighDim.SingularPair

end
