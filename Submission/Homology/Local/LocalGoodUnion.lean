/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Homology.Local.LocalGood
import Submission.Homology.MayerVietoris.RelativeMVOpen

/-!
# `LocalGood` for unions (Hatcher 3.27(a), steps 2 and 3)

* `LocalGood.union`: if `A`, `B ⊆ X` are closed and `A`, `B`, `A ∩ B` are locally good in
  degree `n`, so is `A ∪ B`. This is the relative Mayer–Vietoris sequence of the open sets
  `Aᶜ`, `Bᶜ` (`RelativeMVOpen.lean`): the vanishing above the dimension follows from
  `isZero_Hrel_inter_of_isZero`, the uniqueness from `relMV_injective` applied to
  `H_{n+1}(X, (A ∩ B)ᶜ) = 0`.
* `LocalGood.of_finite_convex`: finite unions of compact convex subsets of
  `EU n = ℝⁿ` (`n ≥ 1`) are locally good. Induction on the number of sets over all families
  simultaneously, the intersection of a union with the last set being again a finite union of
  compact convex sets.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable {R : ModuleCat.{u} ℤ} {X : TopCat.{u}}

/-- two successive `HrelMap`s of the identity compose to the `HrelMap` of the identity -/
lemma HrelMap_id_apply_HrelMap_id_apply {A B C : Set X} (h₁ : Set.MapsTo (𝟙 X) A B)
    (h₂ : Set.MapsTo (𝟙 X) B C) (h₃ : Set.MapsTo (𝟙 X) A C) (k : ℕ) (α : Hrel R X A k) :
    HrelMap R (𝟙 X) h₂ k (HrelMap R (𝟙 X) h₁ k α) = HrelMap R (𝟙 X) h₃ k α := by
  rw [← ModuleCat.comp_apply, ← HrelMap_comp R (𝟙 X) (𝟙 X) h₁ h₂ (mapsTo_comp h₁ h₂) k]
  exact congrArg (fun f : Hrel R X A k ⟶ Hrel R X C k => f α)
    (HrelMap_eq_of_eq R (Category.id_comp (𝟙 X)) _ k)

/-- `HrelMap` of the identity along an equality of subsets is injective -/
lemma HrelMap_id_injective_of_eq {A B : Set X} (e : A = B) (h : Set.MapsTo (𝟙 X) A B)
    (k : ℕ) : Function.Injective (HrelMap R (𝟙 X) h k) := by
  have : HrelMap R (𝟙 X) h k = (HrelIsoOfEq R X e k).hom := rfl
  rw [this]
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

namespace LocalGood

variable {n : ℕ}

/-- **Union step (Hatcher 3.27(a), step 2).** If `A`, `B` are closed and `A`, `B`, `A ∩ B`
are locally good in degree `n`, then so is `A ∪ B`. -/
theorem union {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (gA : LocalGood R X n A)
    (gB : LocalGood R X n B) (gAB : LocalGood R X n (A ∩ B)) : LocalGood R X n (A ∪ B) := by
  have hP : IsOpen Aᶜ := hA.isOpen_compl
  have hQ : IsOpen Bᶜ := hB.isOpen_compl
  have hvan : ∀ i, n < i → IsZero (Hrel R X (Aᶜ ∩ Bᶜ) i) := fun i hi =>
    isZero_Hrel_inter_of_isZero R hP hQ i
      ((gAB.isZero (by omega)).of_iso (HrelIsoOfEq R X (Set.compl_inter A B) (i + 1)).symm)
      (gA.isZero hi) (gB.isZero hi)
  refine ⟨fun i hi => (hvan i hi).of_iso (HrelIsoOfEq R X (Set.compl_union A B) i),
    fun α hα => ?_⟩
  -- transport `α` to `H_n(X, Aᶜ ∩ Bᶜ)`
  have hmt : Set.MapsTo (𝟙 X) (A ∪ B)ᶜ (Aᶜ ∩ Bᶜ) := mapsTo_id_of_subset (Set.compl_union A B).le
  apply HrelMap_id_injective_of_eq (Set.compl_union A B) hmt n
  rw [map_zero]
  refine relMV_injective R hP hQ n
    ((gAB.isZero (Nat.lt_succ_self n)).of_iso
      (HrelIsoOfEq R X (Set.compl_inter A B) (n + 1)).symm)
    _ ?_ ?_
  · rw [HrelMap_id_apply_HrelMap_id_apply hmt _ (mapsTo_id_of_subset (Set.compl_subset_compl.2
      Set.subset_union_left))]
    refine gA.eq_zero fun x hx => ?_
    rw [HrelMap_id_apply_HrelMap_id_apply _ _ (compl_mapsTo (Or.inl hx : x ∈ A ∪ B))]
    exact hα x (Or.inl hx)
  · rw [HrelMap_id_apply_HrelMap_id_apply hmt _ (mapsTo_id_of_subset (Set.compl_subset_compl.2
      Set.subset_union_right))]
    refine gB.eq_zero fun x hx => ?_
    rw [HrelMap_id_apply_HrelMap_id_apply _ _ (compl_mapsTo (Or.inr hx : x ∈ A ∪ B))]
    exact hα x (Or.inr hx)

/-- **Finite unions of compact convex sets are locally good** in `ℝⁿ`, `n ≥ 1`
(Hatcher 3.27(a), step 3). -/
theorem of_finite_convex (hn : 1 ≤ n) (m : ℕ) (C : Fin m → Set (EU.{u} n))
    (hC : ∀ j, Convex ℝ (C j) ∧ IsCompact (C j)) :
    LocalGood R (TopCat.of (EU n)) n (⋃ j, C j) := by
  induction m with
  | zero => exact (empty _ _).of_eq (Set.iUnion_of_empty C).symm
  | succ m ih =>
    refine (union (isClosed_iUnion_of_finite fun j => (hC (Fin.castSucc j)).2.isClosed)
      (hC (Fin.last m)).2.isClosed (ih (C ∘ Fin.castSucc) fun j => hC _)
      (of_convex hn (hC (Fin.last m)).1 (hC (Fin.last m)).2) ?_).of_eq
      (Set.iUnion_fin_add_one_eq_iUnion_castSucc C).symm
    refine (ih (fun j => C (Fin.castSucc j) ∩ C (Fin.last m)) fun j =>
      ⟨(hC _).1.inter (hC _).1, (hC _).2.inter_right (hC _).2.isClosed⟩).of_eq ?_
    exact (Set.iUnion_inter (C (Fin.last m)) (C ∘ Fin.castSucc)).symm

end LocalGood

end PoincareHighDim.SingularPair

end
