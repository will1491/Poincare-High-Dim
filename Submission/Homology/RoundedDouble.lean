import Submission.Topology.RoundedDouble
import Submission.Topology.ChartDiskComplement
import Submission.Homology.PuncturedFilling

/-!
# The homological inputs from a rounded product

If the base `{g ≤ 0}` is simply connected and acyclic, so is the rounded filling
`{g x + t² ≤ 0}`. Removing a chart disk from that filling produces a simply connected
space with zero integral homology relative to the new sphere boundary. These are the
interior inputs to the h-cobordism theorem; regular levels and the upper boundary are
handled separately.
-/

namespace PoincareHighDim.RoundedDouble

open Set
open scoped ContinuousMap

universe u

variable {X : Type u} [TopologicalSpace X]

theorem simplyConnectedSpace_filling (g : X → ℝ) [SimplyConnectedSpace (base g)] :
    SimplyConnectedSpace (filling g) :=
  (homotopyEquivBase g).simplyConnectedSpace

theorem acyclic_filling (R : ModuleCat.{u} ℤ) (g : X → ℝ)
    (h : SingularPair.Acyclic R (TopCat.of (base g))) :
    SingularPair.Acyclic R (TopCat.of (filling g)) :=
  SingularPair.Acyclic.of_homotopyEquiv R (homotopyEquivBase g) h

/-- The simply connected and relative-homology conditions for the punctured filling. -/
theorem punctured_filling_hcobordism_input [T2Space X] {d : ℕ} (hd : 3 ≤ d)
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) (X × ℝ)]
    (g : X → ℝ) [SimplyConnectedSpace (base g)]
    (hacyclic : SingularPair.Acyclic SingularPair.Z.{u} (TopCat.of (base g)))
    {e : Disk d → X × ℝ} (he : IsChartDisk e) (hD : range e ⊆ filling g) :
    SimplyConnectedSpace (filling g \ e '' diskInterior d : Set (X × ℝ)) ∧
      RelHomologyVanishes (filling g \ e '' diskInterior d : Set (X × ℝ))
        (Subtype.val ⁻¹' (e '' diskSphere d)) := by
  have hB : IsSimplyConnected (filling g) := simplyConnectedSpace_filling g
  exact ⟨isSimplyConnected_sdiff_chartDisk hd he hD hB,
    SingularPair.relHomologyVanishes_puncturedFilling he hD
      (acyclic_filling SingularPair.Z g hacyclic)⟩

end PoincareHighDim.RoundedDouble
