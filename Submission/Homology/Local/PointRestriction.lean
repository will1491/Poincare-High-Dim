/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Homology.Local.ChartTransport

/-!
# Point restrictions of absolute homology classes

For a space `X` and a class `c ∈ H_n(X)`, the *point restriction* of `c` at `x ∈ X` is its image
`ptRes R X n c x ∈ H_n(X, X ∖ {x})` under `relπ`.

* `ptRes_eq_zero_of_notMem`: a class coming from `H_n(K)` has vanishing point restrictions
  outside `K`;
* `ptRes_res`: the point restriction factors through `H_n(X, X ∖ A)` for `x ∈ A`;
* `isClopen_ptRes_eq_zero`: on a Hausdorff space charted on `ℝⁿ`, `n ≥ 1`, the set of points
  where the point restriction of `c` vanishes is clopen (via the chart balls of
  `exists_chartBall_isIso_ptRes`);
* `ptRes_eq_zero_of_exists`: on a connected such space, one vanishing point restriction forces
  all of them to vanish.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

/-! ### Definition and elementary properties -/

/-- the point restriction `H_n(X) → H_n(X, X ∖ {x})` of a class -/
abbrev ptRes (X : TopCat.{u}) (n : ℕ) (c : H R X n) (x : X) : Hrel R X {x}ᶜ n :=
  relπ R X {x}ᶜ n c

lemma subset_compl_singleton_of_notMem {X : Type*} {K : Set X} {y : X} (hy : y ∉ K) :
    K ⊆ {y}ᶜ :=
  fun _ hz hzy => hy (Set.mem_singleton_iff.1 hzy ▸ hz)

/-- a class supported in `K` has vanishing point restrictions outside `K` -/
lemma ptRes_eq_zero_of_notMem {X : TopCat.{u}} {K : Set X} {n : ℕ} {c : H R X n}
    (hc : c ∈ Set.range (inclMap R X K n)) {y : X} (hy : y ∉ K) : ptRes R X n c y = 0 := by
  obtain ⟨a, rfl⟩ := hc
  have h0 : inclMap R X {y}ᶜ n ≫ relπ R X {y}ᶜ n = 0 :=
    (pair X {y}ᶜ).homologyMap_hom_homologyπ R n
  change relπ R X {y}ᶜ n (inclMap R X K n a) = 0
  rw [inclMap_eq_Hmap, ← inclOfLE_incl (subset_compl_singleton_of_notMem hy), Hmap_comp,
    ModuleCat.comp_apply, ← inclMap_eq_Hmap, ← ModuleCat.comp_apply, h0]
  rfl

/-- the point restriction factors through `H_n(X, X ∖ A)`, morphism form -/
lemma relπ_comp_HrelMap_compl_mapsTo {X : TopCat.{u}} {A : Set X} {x : X} (hx : x ∈ A)
    (n : ℕ) :
    relπ R X Aᶜ n ≫ HrelMap R (𝟙 X) (compl_mapsTo hx) n = relπ R X {x}ᶜ n := by
  rw [relπ_natural R (𝟙 X) (compl_mapsTo hx) n, Hmap_id, Category.id_comp]

/-- the point restriction factors through `H_n(X, X ∖ A)` -/
lemma ptRes_res {X : TopCat.{u}} {A : Set X} {x : X} (hx : x ∈ A) (n : ℕ) (c : H R X n) :
    HrelMap R (𝟙 X) (compl_mapsTo hx) n (relπ R X Aᶜ n c) = ptRes R X n c x := by
  rw [← ModuleCat.comp_apply, relπ_comp_HrelMap_compl_mapsTo R hx n]

/-- if the restriction `H_n(X, X ∖ A) → H_n(X, X ∖ {x})` is injective, the point restriction
at `x` vanishes iff the restriction to `H_n(X, X ∖ A)` does -/
lemma ptRes_eq_zero_iff_of_mono {X : TopCat.{u}} {A : Set X} {x : X} (hx : x ∈ A) (n : ℕ)
    (hmono : Mono (HrelMap R (𝟙 X) (compl_mapsTo hx) n)) (c : H R X n) :
    ptRes R X n c x = 0 ↔ relπ R X Aᶜ n c = 0 := by
  rw [← ptRes_res R hx n c]
  exact map_eq_zero_iff _ ((ModuleCat.mono_iff_injective _).1 hmono)

/-! ### Local constancy on a charted space -/

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- the vanishing of point restrictions is locally constant -/
lemma exists_nhds_ptRes_eq_zero_iff (hn : 1 ≤ n) (c : H R (TopCat.of M) n) (x : M) :
    ∃ U ∈ nhds x, ∀ y ∈ U,
      (ptRes R (TopCat.of M) n c y = 0 ↔ ptRes R (TopCat.of M) n c x = 0) := by
  obtain ⟨D, -, hxD, hiso⟩ := exists_chartBall_isIso_ptRes R hn x
  refine ⟨interior D, isOpen_interior.mem_nhds hxD, fun y hy => ?_⟩
  have hx : x ∈ D := interior_subset hxD
  have hy' : y ∈ D := interior_subset hy
  rw [ptRes_eq_zero_iff_of_mono R hy' n (have := hiso y hy'; inferInstance),
    ptRes_eq_zero_iff_of_mono R hx n (have := hiso x hx; inferInstance)]

/-- the set of points where the point restriction of `c` vanishes is open -/
theorem isOpen_ptRes_eq_zero (hn : 1 ≤ n) (c : H R (TopCat.of M) n) :
    IsOpen {x | ptRes R (TopCat.of M) n c x = 0} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU, hUx⟩ := exists_nhds_ptRes_eq_zero_iff R hn c x
  exact Filter.mem_of_superset hU fun y hy => (hUx y hy).2 hx

/-- the set of points where the point restriction of `c` vanishes is closed -/
theorem isClosed_ptRes_eq_zero (hn : 1 ≤ n) (c : H R (TopCat.of M) n) :
    IsClosed {x | ptRes R (TopCat.of M) n c x = 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU, hUx⟩ := exists_nhds_ptRes_eq_zero_iff R hn c x
  exact Filter.mem_of_superset hU fun y hy hy0 => hx ((hUx y hy).1 hy0)

/-- **Local constancy of point restrictions.** The set of points where the point restriction
of a class `c ∈ H_n(M)` vanishes is clopen. -/
theorem isClopen_ptRes_eq_zero (hn : 1 ≤ n) (c : H R (TopCat.of M) n) :
    IsClopen {x | ptRes R (TopCat.of M) n c x = 0} :=
  ⟨isClosed_ptRes_eq_zero R hn c, isOpen_ptRes_eq_zero R hn c⟩

/-- on a connected charted space, one vanishing point restriction forces all to vanish -/
theorem ptRes_eq_zero_of_exists [ConnectedSpace M] (hn : 1 ≤ n) (c : H R (TopCat.of M) n)
    (h : ∃ x, ptRes R (TopCat.of M) n c x = 0) : ∀ x, ptRes R (TopCat.of M) n c x = 0 :=
  Set.eq_univ_iff_forall.1 ((isClopen_ptRes_eq_zero R hn c).eq_univ h)

end charted

end PoincareHighDim.SingularPair

end
