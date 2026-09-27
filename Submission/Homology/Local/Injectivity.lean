import Submission.Homology.Local.PointRestriction

/-!
# Injectivity of `H_n(M) → H_n(M, M ∖ {x})` for compact connected manifolds

This is the uniqueness half of Hatcher, Theorem 3.26(a): on a compact connected Hausdorff
space charted on `ℝⁿ` (`n ≥ 1`), a class `c ∈ H_n(M)` whose point restriction at a single
point `x` vanishes is zero.

* `relπ_compl_eq_zero_of_forall_ptRes`: for `A ⊆ M` compact, a class in `H_n(M)` whose point
  restrictions vanish at all points of `A` maps to `0` in `H_n(M, M ∖ A)`
  (`LocalGood.of_isCompact`);
* `mono_relπ_compl_singleton`: `H_n(M) → H_n(M, M ∖ {x})` is a monomorphism for `M` compact
  and connected (one vanishing point restriction forces all to vanish by the clopen argument
  `ptRes_eq_zero_of_exists`; then `A := Set.univ` above and `H_n(M, ∅) ≅ H_n(M)`).

Both statements are generic in the coefficient module `R`.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- a class of `H_n(M)` whose point restrictions vanish on a compact set `A` maps to zero in
`H_n(M, M ∖ A)` (Hatcher 3.27(a), uniqueness form, for absolute classes) -/
theorem relπ_compl_eq_zero_of_forall_ptRes (hn : 1 ≤ n) {A : Set M} (hA : IsCompact A)
    (c : H R (TopCat.of M) n) (h : ∀ x ∈ A, ptRes R (TopCat.of M) n c x = 0) :
    relπ R (TopCat.of M) Aᶜ n c = 0 :=
  (LocalGood.of_isCompact R hn hA).2 _ fun x hx => by
    rw [ptRes_res R hx n c]
    exact h x hx

/-- on a compact charted space, a class of `H_n(M)` all of whose point restrictions vanish
is zero -/
theorem eq_zero_of_forall_ptRes [CompactSpace M] (hn : 1 ≤ n) (c : H R (TopCat.of M) n)
    (h : ∀ x, ptRes R (TopCat.of M) n c x = 0) : c = 0 := by
  have h0 := relπ_compl_eq_zero_of_forall_ptRes R hn isCompact_univ c fun x _ => h x
  rw [Set.compl_univ] at h0
  have hmono : Mono (relπ R (TopCat.of M) ∅ n) := by
    have := isIso_relπ_empty R (TopCat.of M) n
    infer_instance
  exact ((ModuleCat.mono_iff_injective (relπ R (TopCat.of M) ∅ n)).1 hmono)
    (h0.trans (map_zero _).symm)

/-- **Hatcher 3.26(a), uniqueness.** On a compact connected Hausdorff space charted on `ℝⁿ`
(`n ≥ 1`), the map `H_n(M) → H_n(M, M ∖ {x})` is injective for every `x`. -/
theorem mono_relπ_compl_singleton (hn : 1 ≤ n) [CompactSpace M] [ConnectedSpace M] (x : M) :
    Mono (relπ R (TopCat.of M) {x}ᶜ n) := by
  rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro c hc
  exact eq_zero_of_forall_ptRes R hn c (ptRes_eq_zero_of_exists R hn c ⟨x, hc⟩)

/-- the injectivity of `H_n(M) → H_n(M, M ∖ {x})`, function form -/
theorem ptRes_injective (hn : 1 ≤ n) [CompactSpace M] [ConnectedSpace M] (x : M) :
    Function.Injective fun c : H R (TopCat.of M) n => ptRes R (TopCat.of M) n c x :=
  (ModuleCat.mono_iff_injective _).1 (mono_relπ_compl_singleton R hn x)

end charted

end PoincareHighDim.SingularPair

end
