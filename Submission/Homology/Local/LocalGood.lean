import Submission.Homology.Local.LocalHomology
import Submission.Homology.Support

/-!
# The local-homology predicate `LocalGood` (Hatcher, Lemma 3.27(a), uniqueness form)

For a coefficient module `R`, a space `X`, a degree `n` and a subset `A ⊆ X` we say that `A` is
*locally good* (`LocalGood R X n A`) when

* `H_i(X, X ∖ A) = 0` for every `i > n`, and
* a class `α ∈ H_n(X, X ∖ A)` all of whose *point restrictions*
  `H_n(X, X ∖ A) → H_n(X, X ∖ {x})`, `x ∈ A`, vanish is itself zero.

This is exactly the content of Hatcher's Lemma 3.27(a) (vanishing above the dimension and
uniqueness of classes with prescribed point restrictions); the existence half of 3.27 is never
needed.

This file provides

* accessors `LocalGood.isZero`, `LocalGood.eq_zero`, `LocalGood.of_eq`;
* `LocalGood.empty`: the empty set is locally good in every space and degree;
* `LocalGood.of_mono_ptRes`: a set with the vanishing property and one point whose point
  restriction is a monomorphism is locally good;
* `LocalGood.of_iso`, `LocalGood.of_iso_map`: transport of `LocalGood` along a family of
  isomorphisms of relative homology groups compatible with the point restrictions;
* the base cases in `EU n := ULift.{u} (EuclideanSpace ℝ (Fin n))`, `n ≥ 1`:
  `LocalGood.singleton` (points) and `LocalGood.of_convex` (compact convex sets).
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

variable (R : ModuleCat.{u} ℤ)

/-- **Hatcher 3.27(a), uniqueness form.** `A ⊆ X` is *locally good in degree `n`* if
`H_i(X, X ∖ A) = 0` for `i > n` and a class in `H_n(X, X ∖ A)` whose point restrictions to
`H_n(X, X ∖ {x})` vanish for every `x ∈ A` is zero. -/
def LocalGood (X : TopCat.{u}) (n : ℕ) (A : Set X) : Prop :=
  (∀ i, n < i → IsZero (Hrel R X Aᶜ i)) ∧
    ∀ α : Hrel R X Aᶜ n, (∀ x (hx : x ∈ A), HrelMap R (𝟙 X) (compl_mapsTo hx) n α = 0) → α = 0

variable {R}

/-- an element of a zero module is zero -/
lemma eq_zero_of_isZero {M : ModuleCat.{u} ℤ} (h : IsZero M) (m : M) : m = 0 :=
  (ModuleCat.isZero_iff_subsingleton.1 h).elim m 0

namespace LocalGood

variable {X : TopCat.{u}} {n : ℕ} {A : Set X}

/-- vanishing above the dimension -/
theorem isZero (h : LocalGood R X n A) {i : ℕ} (hi : n < i) : IsZero (Hrel R X Aᶜ i) :=
  h.1 i hi

/-- a class with vanishing point restrictions is zero -/
theorem eq_zero (h : LocalGood R X n A) {α : Hrel R X Aᶜ n}
    (hα : ∀ x (hx : x ∈ A), HrelMap R (𝟙 X) (compl_mapsTo hx) n α = 0) : α = 0 :=
  h.2 α hα

theorem of_eq (h : LocalGood R X n A) {A' : Set X} (e : A = A') : LocalGood R X n A' :=
  e ▸ h

/-- the empty set is locally good in every space and every degree -/
theorem empty (X : TopCat.{u}) (n : ℕ) : LocalGood R X n (∅ : Set X) := by
  refine ⟨fun i _ => ?_, fun α _ => eq_zero_of_isZero ?_ α⟩ <;>
  · rw [Set.compl_empty]
    exact isZero_Hrel_univ R X _

/-- if `A` satisfies the vanishing condition and the point restriction at a single point
`x ∈ A` is a monomorphism, then `A` is locally good -/
theorem of_mono_ptRes (hvan : ∀ i, n < i → IsZero (Hrel R X Aᶜ i)) {x : X} (hx : x ∈ A)
    (hmono : Mono (HrelMap R (𝟙 X) (compl_mapsTo hx) n)) : LocalGood R X n A := by
  refine ⟨hvan, fun α hα => ?_⟩
  apply (ModuleCat.mono_iff_injective _).1 hmono
  rw [hα x hx, map_zero]

/-- **Transport along isomorphisms.** If the relative groups of `(X, X ∖ A)` and
`(Y, Y ∖ B)` are isomorphic in every degree, and every point `y ∈ B` is matched by a point
`x ∈ A` together with a map `H_n(X, X ∖ {x}) → H_n(Y, Y ∖ {y})` making the point restrictions
commute, then `LocalGood` for `B` implies `LocalGood` for `A`. -/
theorem of_iso {Y : TopCat.{u}} {B : Set Y} (i : ∀ k, Hrel R X Aᶜ k ≅ Hrel R Y Bᶜ k)
    (hpt : ∀ y (hy : y ∈ B), ∃ x, ∃ hx : x ∈ A, ∃ j : Hrel R X {x}ᶜ n ⟶ Hrel R Y {y}ᶜ n,
      (i n).hom ≫ HrelMap R (𝟙 Y) (compl_mapsTo hy) n =
        HrelMap R (𝟙 X) (compl_mapsTo hx) n ≫ j)
    (hB : LocalGood R Y n B) : LocalGood R X n A := by
  refine ⟨fun k hk => (hB.1 k hk).of_iso (i k), fun α hα => ?_⟩
  have hβ : (i n).hom α = 0 := by
    refine hB.2 _ fun y hy => ?_
    obtain ⟨x, hx, j, hj⟩ := hpt y hy
    rw [← ModuleCat.comp_apply, hj, ModuleCat.comp_apply, hα x hx, map_zero]
  apply (ModuleCat.mono_iff_injective (i n).hom).1 inferInstance
  rw [hβ, map_zero]

/-- `of_iso` for a map of points `f : X → Y` sending `A` onto `B`, with the point maps
given by a family `j` indexed by `x ∈ A` -/
theorem of_iso_map {Y : TopCat.{u}} {B : Set Y} (f : X → Y) (hf : ∀ x ∈ A, f x ∈ B)
    (hsurj : ∀ y ∈ B, ∃ x ∈ A, f x = y) (i : ∀ k, Hrel R X Aᶜ k ≅ Hrel R Y Bᶜ k)
    (j : ∀ x, x ∈ A → (Hrel R X {x}ᶜ n ⟶ Hrel R Y {f x}ᶜ n))
    (hj : ∀ x (hx : x ∈ A), (i n).hom ≫ HrelMap R (𝟙 Y) (compl_mapsTo (hf x hx)) n =
      HrelMap R (𝟙 X) (compl_mapsTo hx) n ≫ j x hx)
    (hB : LocalGood R Y n B) : LocalGood R X n A := by
  refine of_iso i (fun y hy => ?_) hB
  obtain ⟨x, hx, rfl⟩ := hsurj y hy
  exact ⟨x, hx, j x hx, hj x hx⟩

/-- `LocalGood` is invariant under isomorphisms in both directions (bijective point matching) -/
theorem iff_of_iso {Y : TopCat.{u}} {B : Set Y} (i : ∀ k, Hrel R X Aᶜ k ≅ Hrel R Y Bᶜ k)
    (hpt : ∀ y (hy : y ∈ B), ∃ x, ∃ hx : x ∈ A, ∃ j : Hrel R X {x}ᶜ n ≅ Hrel R Y {y}ᶜ n,
      (i n).hom ≫ HrelMap R (𝟙 Y) (compl_mapsTo hy) n =
        HrelMap R (𝟙 X) (compl_mapsTo hx) n ≫ j.hom)
    (hpt' : ∀ x (hx : x ∈ A), ∃ y, ∃ hy : y ∈ B, ∃ j : Hrel R X {x}ᶜ n ≅ Hrel R Y {y}ᶜ n,
      (i n).hom ≫ HrelMap R (𝟙 Y) (compl_mapsTo hy) n =
        HrelMap R (𝟙 X) (compl_mapsTo hx) n ≫ j.hom) :
    LocalGood R X n A ↔ LocalGood R Y n B := by
  constructor
  · refine fun hA => of_iso (fun k => (i k).symm) (fun x hx => ?_) hA
    obtain ⟨y, hy, j, hj⟩ := hpt' x hx
    refine ⟨y, hy, j.inv, ?_⟩
    rw [Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hj, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · exact fun hB => of_iso i (fun y hy => by
      obtain ⟨x, hx, j, hj⟩ := hpt y hy
      exact ⟨x, hx, j.hom, hj⟩) hB

/-! ### Base cases in Euclidean space -/

/-- **Compact convex sets are locally good.** For `n ≥ 1` and a compact convex
`C ⊆ ℝⁿ`, `H_i(ℝⁿ, ℝⁿ ∖ C) = 0` for `i > n` and point restrictions detect classes in degree
`n`. -/
theorem of_convex {n : ℕ} (hn : 1 ≤ n) {C : Set (EU.{u} n)} (hC : Convex ℝ C)
    (hCc : IsCompact C) : LocalGood R (TopCat.of (EU n)) n C := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact empty _ _
  · exact of_mono_ptRes (fun i hi => isZero_Hrel_compl_convex R hC hCc ⟨x, hx⟩ hi) hx
      (have := isIso_ptRes_of_convex R hn hC hCc hx n; inferInstance)

/-- **Points are locally good** in `ℝⁿ`, `n ≥ 1`. -/
theorem singleton {n : ℕ} (hn : 1 ≤ n) (x : EU.{u} n) :
    LocalGood R (TopCat.of (EU n)) n {x} :=
  of_convex hn (convex_singleton x) isCompact_singleton

end LocalGood

end PoincareHighDim.SingularPair

end
