import Submission.Homology.Punctures.ChartDiskRetract
import Submission.Homology.Punctures.DiskExcision
import Submission.Homology.Punctures.PuncturedAcyclic
import Submission.Homology.Punctures.FundamentalClass
import Submission.Homology.Relative.PairVanishing

/-!
# Vanishing of `H_*(W, ∂₀W; ℤ)` for the strip between two chart disks

Let `M` be a compact Hausdorff space charted on `ℝⁿ`, `n ≥ 2`, homotopy equivalent to `Sⁿ`, and
let `e₀, e₁ : Disk n → M` be two chart disks with disjoint ranges.  Write
`U_i := e_i '' diskInterior n` for the open disks, `D₀ := range e₀` for the first closed disk,
`S₀ := e₀ '' diskSphere n` for its boundary sphere and `W := (U₀ ∪ U₁)ᶜ` for the strip.  Then
`H_k(W, S₀; ℤ) = 0` for every `k` (`relHomologyVanishes_compl_chartDisks`).

The proof assembles the earlier modules:

* `HrelWIso` (`Submission.Homology.Punctures.DiskExcision`): excision and relative homotopy invariance give
  `H_k(W, S₀) ≅ H_k(M ∖ U₁, D₀)`;
* `M ∖ U₁` is a deformation retract of `M ∖ {c₁}`, `c₁ := e₁ (diskCenter n)`
  (`IsChartDisk.isHomotopyEquivInclusion_compl_diskInterior` of
  `Submission.Homology.Punctures.ChartDiskRetract`), and `M ∖ {c₁}` is acyclic
  (`acyclic_compl_singleton_Z` of `Submission.Homology.Punctures.FundamentalClass`, the consequence of the
  fundamental class of `M`), so `M ∖ U₁` is acyclic;
* `D₀ ⊆ M ∖ U₁` is contractible (`IsChartDisk.contractibleSpace_range`), so the long exact
  sequence of the pair gives `H_k(M ∖ U₁, D₀) = 0`
  (`isZero_Hrel_of_contractible_of_acyclic'` of `Submission.Homology.Punctures.PuncturedAcyclic`).
-/

open CategoryTheory Limits Set
open scoped ContinuousMap

universe u

namespace PoincareHighDim.SingularPair

section chartDisks

variable {n : ℕ} {M : Type u} {e₀ e₁ : Disk n → M}

/-- The first closed disk lies in the complement of the second open disk. -/
theorem range_subset_compl_image_diskInterior (hdisj : Disjoint (range e₀) (range e₁)) :
    range e₀ ⊆ (e₁ '' diskInterior n)ᶜ :=
  fun _ hx h => Set.disjoint_left.1 hdisj hx (image_subset_range _ _ h)

variable [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The first closed disk `D₀`, viewed as a subset of `M ∖ U₁`, is contractible. -/
theorem contractibleSpace_preimage_val_range (h₀ : IsChartDisk e₀)
    (hdisj : Disjoint (range e₀) (range e₁)) :
    ContractibleSpace (Subtype.val ⁻¹' (range e₀) : Set ((e₁ '' diskInterior n)ᶜ : Set M)) :=
  have := h₀.contractibleSpace_range
  (homeomorphPreimageVal (range_subset_compl_image_diskInterior hdisj)).contractibleSpace

variable [CompactSpace M]

/-- **The complement of an open chart disk is acyclic** (integral coefficients): for `n ≥ 2`,
`M` compact Hausdorff, charted on `ℝⁿ` and homotopy equivalent to `Sⁿ`, and a chart disk `e₁`,
`H_k(M ∖ U₁; ℤ) = 0` for `k ≥ 1` and `H̃₀(M ∖ U₁; ℤ) = 0`, since `M ∖ U₁` is a deformation
retract of the punctured space `M ∖ {e₁ 0}`. -/
theorem acyclic_compl_image_diskInterior_Z (hn : 2 ≤ n) (e : M ≃ₕ Sph n)
    (h₁ : IsChartDisk e₁) :
    Acyclic Z.{u} (TopCat.of ((e₁ '' diskInterior n)ᶜ : Set M)) :=
  acyclic_of_homotopyEquivInclusion Z h₁.isHomotopyEquivInclusion_compl_diskInterior
    (acyclic_compl_singleton_Z hn e (e₁ (diskCenter n)))

/-- `H_k(M ∖ U₁, D₀; ℤ) = 0`: the pair of an acyclic space and a contractible subspace. -/
theorem isZero_Hrel_compl_image_diskInterior_range (hn : 2 ≤ n) (e : M ≃ₕ Sph n)
    (h₀ : IsChartDisk e₀) (h₁ : IsChartDisk e₁) (hdisj : Disjoint (range e₀) (range e₁))
    (k : ℕ) :
    IsZero (Hrel Z.{u} (TopCat.of ((e₁ '' diskInterior n)ᶜ : Set M))
      (Subtype.val ⁻¹' (range e₀)) k) :=
  have := contractibleSpace_preimage_val_range h₀ hdisj
  isZero_Hrel_of_contractible_of_acyclic' Z (acyclic_compl_image_diskInterior_Z hn e h₁) k

/-- `H_k(W, S₀; ℤ) = 0` for the strip `W = (U₀ ∪ U₁)ᶜ` and its first boundary sphere `S₀`, by
excision (`HrelWIso`) from `isZero_Hrel_compl_image_diskInterior_range`. -/
theorem isZero_Hrel_compl_chartDisks (hn : 2 ≤ n) (e : M ≃ₕ Sph n)
    (h₀ : IsChartDisk e₀) (h₁ : IsChartDisk e₁) (hdisj : Disjoint (range e₀) (range e₁))
    (k : ℕ) :
    IsZero (Hrel Z.{u} (TopCat.of ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M))
      (Subtype.val ⁻¹' (e₀ '' diskSphere n)) k) :=
  (isZero_Hrel_compl_image_diskInterior_range hn e h₀ h₁ hdisj k).of_iso
    (HrelWIso Z h₀ hdisj k)

/-- **Homological input for the h-cobordism theorem.**  For `n ≥ 2`, `M` compact Hausdorff,
charted on `ℝⁿ` and homotopy equivalent to `Sⁿ`, and two chart disks `e₀, e₁` with disjoint
ranges, `H_*(W, S₀; ℤ) = 0`, where `W = (U₀ ∪ U₁)ᶜ` is the strip and `S₀ ⊆ W` its first
boundary sphere (as the subset `Subtype.val ⁻¹' (e₀ '' diskSphere n)` of the subtype `W`). -/
theorem relHomologyVanishes_compl_chartDisks (hn : 2 ≤ n) (e : M ≃ₕ Sph n)
    (h₀ : IsChartDisk e₀) (h₁ : IsChartDisk e₁) (hdisj : Disjoint (range e₀) (range e₁)) :
    RelHomologyVanishes ((e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ : Set M)
      (Subtype.val ⁻¹' (e₀ '' diskSphere n)) :=
  fun k => isZero_Hrel_compl_chartDisks hn e h₀ h₁ hdisj k

end chartDisks

end PoincareHighDim.SingularPair
