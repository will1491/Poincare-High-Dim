import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient

/-!
# Identifying spaces obtained by collapsing the same set

Two quotient maps with the same fibers have homeomorphic targets. In particular, a
continuous surjection from a compact space that collapses exactly a subset `K` has the
same target, up to homeomorphism, as any other such surjection. This is the quotient step
in Brown's cellular shrinking argument.
-/

namespace PoincareHighDim

open Set Topology

/-- A map identifies all points of `K`, and makes no other identifications. -/
def CollapsesExactly {X Y : Type*} (f : X → Y) (K : Set X) : Prop :=
  ∀ x y, f x = f y ↔ x = y ∨ x ∈ K ∧ y ∈ K

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Quotient maps with the same fibers identify their target spaces homeomorphically. -/
noncomputable def quotientHomeomorphOfSameFibers {f : X → Y} {g : X → Z}
    (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (h : ∀ x y, f x = f y ↔ g x = g y) : Y ≃ₜ Z :=
  (hf.homeomorph (f := ⟨f, hf.continuous⟩)).symm.trans
    ((Homeomorph.Quotient.congrRight h).trans (hg.homeomorph (f := ⟨g, hg.continuous⟩)))

theorem quotientHomeomorphOfSameFibers_apply {f : X → Y} {g : X → Z}
    (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (h : ∀ x y, f x = f y ↔ g x = g y) (x : X) :
    quotientHomeomorphOfSameFibers hf hg h (f x) = g x := by
  change (hg.homeomorph (f := ⟨g, hg.continuous⟩)) ((Homeomorph.Quotient.congrRight h)
    ((hf.homeomorph (f := ⟨f, hf.continuous⟩)).symm (f x))) = g x
  have hx : (hf.homeomorph (f := ⟨f, hf.continuous⟩)) (Quotient.mk (Setoid.ker f) x) = f x := rfl
  rw [← hx, Homeomorph.symm_apply_apply]
  rfl

/-- The compact Hausdorff version requires only continuous surjections. -/
noncomputable def homeomorphOfSameFibers [CompactSpace X] [T2Space Y] [T2Space Z]
    {f : X → Y} {g : X → Z} (hf : Continuous f) (hfs : Function.Surjective f)
    (hg : Continuous g) (hgs : Function.Surjective g)
    (h : ∀ x y, f x = f y ↔ g x = g y) : Y ≃ₜ Z :=
  quotientHomeomorphOfSameFibers (IsQuotientMap.of_surjective_continuous hfs hf)
    (IsQuotientMap.of_surjective_continuous hgs hg) h

/-- Collapsing precisely the same subset produces homeomorphic target spaces. -/
theorem nonempty_homeomorph_of_collapsesExactly [CompactSpace X] [T2Space Y] [T2Space Z]
    {f : X → Y} {g : X → Z} {K : Set X}
    (hf : Continuous f) (hfs : Function.Surjective f)
    (hg : Continuous g) (hgs : Function.Surjective g)
    (hfK : CollapsesExactly f K) (hgK : CollapsesExactly g K) : Nonempty (Y ≃ₜ Z) :=
  ⟨homeomorphOfSameFibers hf hfs hg hgs (fun x y => (hfK x y).trans (hgK x y).symm)⟩

end PoincareHighDim
