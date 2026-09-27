import Submission.Homology.Support
import Submission.Homology.MayerVietoris.RelativeMVOpen
import Submission.Homology.Local.ChartTransport
import Submission.Homology.Local.PointRestriction
import Submission.Homology.Local.Injectivity
import Submission.Homology.Spheres.SphereHomology

/-!
# Non-compact charted spaces have vanishing top homology (Hatcher 3.29, contrapositive)

For a connected Hausdorff space `M` charted on `ℝⁿ` (`n ≥ 1`) which is *not* compact we show
`H_n(M; R) = 0`. Consequently a space homotopy equivalent to `Sⁿ` (so `H_n(M; ℤ) ≅ ℤ ≠ 0`)
is compact.

The proof replaces the long exact sequence of a triple in Hatcher's argument by relative
Mayer–Vietoris injectivity (`relMV_injective`) for the open sets `U := interior K'` and
`V := (closure U)ᶜ`, where `K'` is a compact neighbourhood of a compact set `K` carrying a
given class `c ∈ H_n(M)` (`exists_isCompact_mem_range_inclMap`):

* `H_{n+1}(M, U ∪ V) = 0` because `(U ∪ V)ᶜ` is compact (`LocalGood.of_isCompact`);
* the `U`-component of `c` vanishes because `c` factors through `H_n(K)`, `K ⊆ U`;
* the `V`-component vanishes because all point restrictions of `c` vanish: one of them does
  (at a point outside `K`, which exists as `M` is not compact) and the vanishing set is clopen
  (`ptRes_eq_zero_of_exists`), so `relπ_compl_eq_zero_of_forall_ptRes` applies to the compact
  set `closure U`;
* `U ∩ V = ∅` and `H_n(M, ∅) ≅ H_n(M)`, so `c = 0`.

No second countability or paracompactness is used anywhere.
-/

open CategoryTheory Limits
open scoped ContinuousMap

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

/-! ### Bookkeeping -/

/-- a class coming from `H_n(K)` maps to zero in `H_n(X, B)` whenever `K ⊆ B` -/
lemma relπ_eq_zero_of_mem_range_inclMap {X : TopCat.{u}} {K B : Set X} (hKB : K ⊆ B) {n : ℕ}
    {c : H R X n} (hc : c ∈ Set.range (inclMap R X K n)) : relπ R X B n c = 0 := by
  obtain ⟨a, rfl⟩ := hc
  have h0 : inclMap R X B n ≫ relπ R X B n = 0 :=
    (pair X B).homologyMap_hom_homologyπ R n
  change relπ R X B n (inclMap R X K n a) = 0
  rw [inclMap_eq_Hmap, ← inclOfLE_incl hKB, Hmap_comp, ModuleCat.comp_apply, ← inclMap_eq_Hmap,
    ← ModuleCat.comp_apply, h0]
  rfl

/-- `relπ` is compatible with enlarging the subspace -/
lemma relπ_comp_HrelMap_id {X : TopCat.{u}} {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    relπ R X A n ≫ HrelMap R (𝟙 X) (id_mapsTo h) n = relπ R X B n := by
  rw [relπ_natural, Hmap_id, Category.id_comp]

/-- **Relative Mayer–Vietoris with empty intersection.** If `P`, `Q` are disjoint open sets with
`H_{n+1}(X, P ∪ Q) = 0`, a class of `H_n(X)` vanishing in both `H_n(X, P)` and `H_n(X, Q)` is
zero. -/
theorem eq_zero_of_relπ_eq_zero_of_isOpen {X : TopCat.{u}} {P Q : Set X} (hP : IsOpen P)
    (hQ : IsOpen Q) (hPQ : P ∩ Q = ∅) {n : ℕ} (h : IsZero (Hrel R X (P ∪ Q) (n + 1)))
    (c : H R X n) (hcP : relπ R X P n c = 0) (hcQ : relπ R X Q n c = 0) : c = 0 := by
  have hmono : Mono (relπ R X (P ∩ Q) n) := by
    rw [hPQ]
    have := isIso_relπ_empty R X n
    infer_instance
  have ha : relπ R X (P ∩ Q) n c = 0 := by
    refine relMV_injective R hP hQ n h _ ?_ ?_
    · rw [← ModuleCat.comp_apply, relπ_comp_HrelMap_id R Set.inter_subset_left n, hcP]
    · rw [← ModuleCat.comp_apply, relπ_comp_HrelMap_id R Set.inter_subset_right n, hcQ]
  exact ((ModuleCat.mono_iff_injective (relπ R X (P ∩ Q) n)).1 hmono)
    (ha.trans (map_zero _).symm)

/-! ### Hatcher 3.29, contrapositive -/

/-- on a non-compact space, every compact set misses a point -/
lemma exists_notMem_of_not_compactSpace {M : Type*} [TopologicalSpace M] (hM : ¬ CompactSpace M)
    {K : Set M} (hK : IsCompact K) : ∃ y, y ∉ K := by
  by_contra h
  refine hM (isCompact_univ_iff.1 ?_)
  have hKu : K = Set.univ := Set.eq_univ_of_forall fun y => by_contra fun hy => h ⟨y, hy⟩
  exact hKu ▸ hK

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- **Hatcher 3.29 (contrapositive).** A connected Hausdorff space charted on `ℝⁿ`, `n ≥ 1`,
which is not compact has `H_n(M; R) = 0`. -/
theorem isZero_H_of_not_compactSpace (hn : 1 ≤ n) [ConnectedSpace M] (hM : ¬ CompactSpace M) :
    IsZero (H R (TopCat.of M) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  suffices h : ∀ c : H R (TopCat.of M) n, c = 0 from ⟨fun a b => (h a).trans (h b).symm⟩
  intro c
  have := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  -- the class `c` lives on a compact set `K`, inside the interior `U` of a compact `K'`
  obtain ⟨K, hK, hc⟩ := exists_isCompact_mem_range_inclMap R (TopCat.of M) n c
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  set U : Set M := interior K' with hUdef
  set V : Set M := (closure U)ᶜ with hVdef
  have hU : IsOpen U := isOpen_interior
  have hV : IsOpen V := isClosed_closure.isOpen_compl
  have hclU : closure U ⊆ K' := closure_minimal interior_subset hK'.isClosed
  have hclU_compact : IsCompact (closure U) := hK'.of_isClosed_subset isClosed_closure hclU
  have hUV : U ∩ V = ∅ :=
    Set.disjoint_iff_inter_eq_empty.1 (disjoint_compl_right.mono_left subset_closure)
  -- the complement of `U ∪ V` is compact, so `H_{n+1}(M, U ∪ V) = 0`
  have hA : IsCompact (U ∪ V)ᶜ := by
    refine hK'.of_isClosed_subset (hU.union hV).isClosed_compl fun x hx => ?_
    exact hclU (by_contra fun hx' => hx (Or.inr hx'))
  have hzero : IsZero (Hrel R (TopCat.of M) (U ∪ V) (n + 1)) := by
    have := (LocalGood.of_isCompact R hn hA).1 (n + 1) (by omega)
    rwa [compl_compl] at this
  -- the `U`-component of `c` vanishes since `c` comes from `K ⊆ U`
  have hcU : relπ R (TopCat.of M) U n c = 0 := relπ_eq_zero_of_mem_range_inclMap R hKK' hc
  -- the `V`-component vanishes since all point restrictions of `c` vanish
  obtain ⟨y, hy⟩ := exists_notMem_of_not_compactSpace hM hK
  have hpt : ∀ x, ptRes R (TopCat.of M) n c x = 0 :=
    ptRes_eq_zero_of_exists R hn c ⟨y, ptRes_eq_zero_of_notMem R hc hy⟩
  have hcV : relπ R (TopCat.of M) V n c = 0 :=
    relπ_compl_eq_zero_of_forall_ptRes R hn hclU_compact c fun x _ => hpt x
  exact eq_zero_of_relπ_eq_zero_of_isOpen R hU hV hUV hzero c hcU hcV

end charted

/-! ### Spaces homotopy equivalent to a sphere are compact -/

/-- the coefficient module `Z = ℤ` is not zero -/
theorem not_isZero_Z : ¬ IsZero (Z.{u}) := by
  intro h
  have := h.eq_zero_of_src (𝟙 Z)
  have h1 := congrArg (fun f : Z ⟶ Z => (f : Z → Z) ⟨1⟩) this
  have h2 := congrArg ULift.down h1
  simp at h2

/-- path-connectedness transports along homotopy equivalences -/
theorem pathConnectedSpace_of_homotopyEquiv_target {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace Y] (e : X ≃ₕ Y) : PathConnectedSpace X := by
  obtain ⟨H⟩ := e.left_inv
  refine ⟨⟨e.invFun (Classical.arbitrary Y)⟩, fun x y => ?_⟩
  have hx : Joined (e.invFun (e.toFun x)) x := ⟨H.evalAt x⟩
  have hy : Joined (e.invFun (e.toFun y)) y := ⟨H.evalAt y⟩
  have hxy : Joined (e.invFun (e.toFun x)) (e.invFun (e.toFun y)) :=
    (PathConnectedSpace.joined (e.toFun x) (e.toFun y)).map e.invFun.continuous
  exact hx.symm.trans (hxy.trans hy)

/-- **Hatcher 3.29 for homotopy spheres.** A Hausdorff space charted on `ℝⁿ`, `n ≥ 1`, which
is homotopy equivalent to `Sⁿ` is compact (its top integral homology is `ℤ ≠ 0`). -/
theorem compactSpace_of_homotopyEquiv_sphere_of_one_le {n : ℕ} (hn : 1 ≤ n) {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : CompactSpace M := by
  have : PathConnectedSpace (Sph n) := Sphere.pathConnectedSpace_of_one_le hn
  have : PathConnectedSpace M := pathConnectedSpace_of_homotopyEquiv_target e
  have : ConnectedSpace M := inferInstance
  by_contra hM
  exact not_isZero_Z ((isZero_H_of_not_compactSpace Z hn hM).of_iso
    (Sphere.H_self_iso_of_homotopyEquiv_sphere Z e (by omega)).symm)

end PoincareHighDim.SingularPair

end
