import Submission.Homology.Local.LocalGoodUnion
import Submission.Homology.Support

/-!
# `LocalGood` for compact subsets of Euclidean space (Hatcher 3.27(a), step 4)

For `n ≥ 1` and an arbitrary compact `A ⊆ EU n = ℝⁿ`, `A` is locally good in degree `n`
(`LocalGood.of_isCompact_EU`): `H_i(ℝⁿ, ℝⁿ ∖ A) = 0` for `i > n`, and a class in
`H_n(ℝⁿ, ℝⁿ ∖ A)` whose point restrictions vanish is zero.

The argument replaces Hatcher's cubes by closed balls. Given `α ∈ H_{j+1}(ℝⁿ, ℝⁿ ∖ A)`, the
boundary `δα ∈ H_j(ℝⁿ ∖ A)` is supported on a compact `K_z ⊆ ℝⁿ ∖ A`
(`exists_isCompact_subset_forall_mem_range`, from `Support.lean`). The disjoint compacts `A`,
`K_z` have disjoint closed `r`-thickenings; a finite `r`-net `F ⊆ A` gives a finite union of
closed balls `K = ⋃ a ∈ F, closedBall a r ⊇ A` disjoint from `K_z`. Since `ℝⁿ` is acyclic, `δα`
lifts to `H_j(ℝⁿ ∖ K)` and then, by exactness, to a class `β ∈ H_{j+1}(ℝⁿ, ℝⁿ ∖ K)` restricting
to `α` (`exists_finset_closedBall_HrelMap_eq`). Finite unions of closed balls are locally good
(`LocalGood.of_finset_convex`, the `Finset`-indexed form of `LocalGood.of_finite_convex`), which
gives both the vanishing above the dimension and, using that the point restriction of a closed
ball at its centre is an isomorphism, the uniqueness statement.
-/

open CategoryTheory Limits Metric

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

/-- a module all of whose elements vanish is a zero object -/
lemma isZero_of_forall_eq_zero {M : ModuleCat.{u} ℤ} (h : ∀ m : M, m = 0) : IsZero M :=
  ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b => (h a).trans (h b).symm⟩

/-! ### Compact support of the homology of a subspace -/

section support

variable {X : TopCat.{u}} {A B : Set X}

/-- the inclusion of a subset `K` of the subspace `A` into a subspace `B ⊇ Subtype.val '' K` -/
def inclSubSub (K : Set (TopCat.of A)) (hKB : Subtype.val '' K ⊆ B) :
    TopCat.of K ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun x => ⟨x.1.1, hKB ⟨x.1, x.2, rfl⟩⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

lemma inclSubSub_inclOfLE (K : Set (TopCat.of A)) (hKB : Subtype.val '' K ⊆ B) (hB : B ⊆ A) :
    inclSubSub K hKB ≫ inclOfLE hB = incl (TopCat.of A) K := rfl

/-- Every homology class of a subspace `A ⊆ X` is supported on a compact `K ⊆ A`: it comes from
`H_k(B)` for every `B` with `K ⊆ B ⊆ A`. -/
theorem exists_isCompact_subset_forall_mem_range (X : TopCat.{u}) (A : Set X) (k : ℕ)
    (c : H R (TopCat.of A) k) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ A ∧ ∀ (B : Set X) (hB : B ⊆ A), K ⊆ B →
      c ∈ Set.range (Hmap R (inclOfLE hB) k) := by
  obtain ⟨K', hK', w, hw⟩ := exists_isCompact_mem_range_inclMap R (TopCat.of A) k c
  refine ⟨Subtype.val '' K', hK'.image continuous_subtype_val, Subtype.coe_image_subset A K',
    fun B hB hKB => ⟨Hmap R (inclSubSub K' hKB) k w, ?_⟩⟩
  rw [← ModuleCat.comp_apply, ← Hmap_comp, inclSubSub_inclOfLE]
  exact hw

end support

/-! ### Finite unions of closed balls -/

variable {n : ℕ}

/-- **Finite unions of compact convex sets are locally good**, `Finset`-indexed form of
`LocalGood.of_finite_convex`. -/
theorem LocalGood.of_finset_convex (hn : 1 ≤ n) {ι : Type*} (F : Finset ι)
    (C : ι → Set (EU.{u} n)) (hC : ∀ a ∈ F, Convex ℝ (C a) ∧ IsCompact (C a)) :
    LocalGood R (TopCat.of (EU n)) n (⋃ a ∈ F, C a) := by
  classical
  induction F using Finset.induction_on generalizing C with
  | empty => exact (LocalGood.empty _ _).of_eq (by simp)
  | insert a F ha ih =>
    rw [Finset.set_biUnion_insert]
    refine LocalGood.union (hC a (Finset.mem_insert_self a F)).2.isClosed
      (isClosed_biUnion_finset fun b hb => (hC b (Finset.mem_insert_of_mem hb)).2.isClosed)
      (LocalGood.of_convex hn (hC a (Finset.mem_insert_self a F)).1
        (hC a (Finset.mem_insert_self a F)).2)
      (ih C fun b hb => hC b (Finset.mem_insert_of_mem hb)) ?_
    rw [Set.inter_iUnion₂]
    exact ih (fun b => C a ∩ C b) fun b hb =>
      ⟨(hC a (Finset.mem_insert_self a F)).1.inter (hC b (Finset.mem_insert_of_mem hb)).1,
        (hC a (Finset.mem_insert_self a F)).2.inter_right
          (hC b (Finset.mem_insert_of_mem hb)).2.isClosed⟩

/-- finite unions of closed balls are locally good in `ℝⁿ`, `n ≥ 1` -/
theorem LocalGood.of_finset_closedBall (hn : 1 ≤ n) (F : Finset (EU.{u} n)) (r : ℝ) :
    LocalGood R (TopCat.of (EU n)) n (⋃ a ∈ F, closedBall a r) :=
  LocalGood.of_finset_convex R hn F (fun a => closedBall a r) fun a _ =>
    ⟨convex_closedBall a r, isCompact_closedBall a r⟩

/-! ### Approximation of a compact set by a finite union of closed balls -/

/-- **Hatcher 3.27(a), step 4, the approximation.** A class `α ∈ H_{j+1}(ℝⁿ, ℝⁿ ∖ A)`, `A`
compact, is the restriction of a class `β ∈ H_{j+1}(ℝⁿ, ℝⁿ ∖ K)` for a finite union `K ⊇ A` of
closed balls of a common positive radius centred at points of `A`. -/
theorem exists_finset_closedBall_HrelMap_eq {A : Set (EU.{u} n)} (hA : IsCompact A) (j : ℕ)
    (α : Hrel R (TopCat.of (EU n)) Aᶜ (j + 1)) :
    ∃ (F : Finset (EU.{u} n)) (r : ℝ), 0 < r ∧ (∀ a ∈ F, a ∈ A) ∧
      ∃ (hsub : A ⊆ ⋃ a ∈ F, closedBall a r)
        (β : Hrel R (TopCat.of (EU n)) (⋃ a ∈ F, closedBall a r)ᶜ (j + 1)),
        HrelMap R (𝟙 (TopCat.of (EU n)))
          (mapsTo_id_of_subset (Set.compl_subset_compl.2 hsub)) (j + 1) β = α := by
  obtain ⟨Kz, hKz, hKzA, hrange⟩ :=
    exists_isCompact_subset_forall_mem_range R (TopCat.of (EU n)) Aᶜ j
      (δ R (TopCat.of (EU n)) Aᶜ j α)
  have hdisj : Disjoint A Kz := Set.disjoint_left.2 fun a ha haz => hKzA haz ha
  obtain ⟨r, hr, hdisj'⟩ := hdisj.exists_cthickenings hA hKz.isClosed
  obtain ⟨F, hFA, hAF⟩ :=
    hA.elim_nhds_subcover (fun a => ball a r) fun a _ => ball_mem_nhds a hr
  have hsub : A ⊆ ⋃ a ∈ F, closedBall a r :=
    hAF.trans (Set.iUnion₂_mono fun a _ => ball_subset_closedBall)
  refine ⟨F, r, hr, hFA, hsub, ?_⟩
  have hKKz : Kz ⊆ (⋃ a ∈ F, closedBall a r)ᶜ := by
    intro z hz hzK
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.1 hzK
    exact Set.disjoint_left.1 hdisj' (closedBall_subset_cthickening (hFA a ha) r hza)
      (self_subset_cthickening Kz hz)
  have hKA : (⋃ a ∈ F, closedBall a r)ᶜ ⊆ Aᶜ := Set.compl_subset_compl.2 hsub
  obtain ⟨γ, hγ⟩ := hrange _ hKA hKKz
  have hγ0 : inclMap R (TopCat.of (EU n)) (⋃ a ∈ F, closedBall a r)ᶜ j γ = 0 := by
    have h0 : δ R (TopCat.of (EU n)) Aᶜ j ≫ inclMap R (TopCat.of (EU n)) Aᶜ j = 0 :=
      (pair (TopCat.of (EU n)) Aᶜ).homologyδ_comp R (j + 1) j rfl
    rw [inclMap_eq_Hmap, ← inclOfLE_incl hKA, Hmap_comp, ModuleCat.comp_apply, hγ,
      ← inclMap_eq_Hmap, ← ModuleCat.comp_apply, h0]
    rfl
  obtain ⟨β, hβ⟩ :=
    (ShortComplex.moduleCat_exact_iff _).1 (les_exact₁ R (TopCat.of (EU n)) _ j) γ hγ0
  refine ⟨β, ?_⟩
  have hmono : Mono (δ R (TopCat.of (EU n)) Aᶜ j) :=
    (les_exact₃ R (TopCat.of (EU n)) Aᶜ j).mono_g_iff.2
      ((isZero_H_EU R n (j + 1) (by omega)).eq_zero_of_src _)
  apply (ModuleCat.mono_iff_injective _).1 hmono
  rw [← ModuleCat.comp_apply, ← δ_natural R (𝟙 (TopCat.of (EU n))) _ j, ModuleCat.comp_apply,
    hβ]
  have hrestr : restr (𝟙 (TopCat.of (EU n))) (mapsTo_id_of_subset hKA) = inclOfLE hKA := by
    ext x
    rfl
  rw [hrestr, hγ]

/-! ### The main theorem -/

/-- **Compact subsets of `ℝⁿ` are locally good** (Hatcher 3.27(a), step 4): for `n ≥ 1` and
`A ⊆ ℝⁿ` compact, `H_i(ℝⁿ, ℝⁿ ∖ A) = 0` for `i > n` and a class in `H_n(ℝⁿ, ℝⁿ ∖ A)` with
vanishing point restrictions is zero. -/
theorem LocalGood.of_isCompact_EU (hn : 1 ≤ n) {A : Set (EU.{u} n)} (hA : IsCompact A) :
    LocalGood R (TopCat.of (EU n)) n A := by
  refine ⟨fun i hi => ?_, fun α hα => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    refine isZero_of_forall_eq_zero fun α => ?_
    obtain ⟨F, r, hr, -, hsub, β, rfl⟩ := exists_finset_closedBall_HrelMap_eq R hA j α
    rw [eq_zero_of_isZero ((LocalGood.of_finset_closedBall R hn F r).isZero hi) β, map_zero]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    obtain ⟨F, r, hr, hF, hsub, β, rfl⟩ := exists_finset_closedBall_HrelMap_eq R hA j α
    have hβ : β = 0 := by
      refine (LocalGood.of_finset_closedBall R hn F r).eq_zero fun x hx => ?_
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 hx
      have hD : closedBall a r ⊆ ⋃ a ∈ F, closedBall a r :=
        Set.subset_iUnion₂ (s := fun a (_ : a ∈ F) => closedBall a r) a ha
      have hβD : HrelMap R (𝟙 (TopCat.of (EU (j + 1))))
          (mapsTo_id_of_subset (Set.compl_subset_compl.2 hD)) (j + 1) β = 0 := by
        have hiso := isIso_ptRes_of_convex R hn (convex_closedBall a r) (isCompact_closedBall a r)
          (mem_closedBall_self hr.le) (j + 1)
        apply (ModuleCat.mono_iff_injective (HrelMap R (𝟙 (TopCat.of (EU (j + 1))))
          (compl_mapsTo (mem_closedBall_self hr.le)) (j + 1))).1 inferInstance
        have ha' : a ∈ closedBall a r := mem_closedBall_self hr.le
        rw [map_zero, HrelMap_id_apply_HrelMap_id_apply _ _ (compl_mapsTo (hD ha')),
          ← HrelMap_id_apply_HrelMap_id_apply
            (mapsTo_id_of_subset (Set.compl_subset_compl.2 hsub)) (compl_mapsTo (hF a ha))
            (compl_mapsTo (hD ha'))]
        exact hα a (hF a ha)
      rw [← HrelMap_id_apply_HrelMap_id_apply (mapsTo_id_of_subset (Set.compl_subset_compl.2 hD))
        (compl_mapsTo hxa) (compl_mapsTo hx), hβD, map_zero]
    rw [hβ, map_zero]

end PoincareHighDim.SingularPair

end
