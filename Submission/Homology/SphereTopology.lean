import Submission.Homology.SingularPair
import Submission.Topology.SphereSimplyConnected

/-!
# Topology of spheres for the Mayer–Vietoris computation

For `Sph n := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1` we record: the poles `N`, `S`,
the open cover by their complements, contractibility of each complement (stereographic
projection, from `Submission.Topology.SphereSimplyConnected`), a homotopy equivalence between the
intersection of the two complements and the equator `Sph n` (radial projection of the first
`n + 1` coordinates, homotopy inverse the inclusion of the equator), path connectedness of
`Sph (n+1)`, and the identification of `Sph 0` with the two-point discrete space.
-/

open Metric Module Set unitInterval
open scoped ContinuousMap

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

/-- the unit sphere in `ℝ^(n+1)` (the project's model of `Sⁿ`) -/
abbrev Sph (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

namespace Sphere

/-! ### Poles and the open cover -/

/-- the north pole `(0, …, 0, 1)` -/
def N (n : ℕ) : Sph n :=
  ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩

/-- the south pole `(0, …, 0, -1)` -/
def S (n : ℕ) : Sph n :=
  ⟨-EuclideanSpace.single (Fin.last n) 1, by simp⟩

@[simp] lemma N_val (n : ℕ) : (N n).1 = EuclideanSpace.single (Fin.last n) 1 := rfl
@[simp] lemma S_val (n : ℕ) : (S n).1 = -EuclideanSpace.single (Fin.last n) 1 := rfl

lemma N_ne_S (n : ℕ) : N n ≠ S n := by
  intro h
  have := congrArg (fun x : Sph n => x.1 (Fin.last n)) h
  simp at this
  norm_num at this

lemma isOpen_compl_singleton {n : ℕ} (x : Sph n) : IsOpen ({x}ᶜ : Set (Sph n)) :=
  _root_.isOpen_compl_singleton

lemma cover (n : ℕ) : ({N n}ᶜ : Set (Sph n)) ∪ {S n}ᶜ = univ := by
  ext x
  simp only [mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
  by_contra h
  simp only [not_or, not_not] at h
  exact N_ne_S n (h.1.symm.trans h.2)

instance contractibleSpace_compl_N (n : ℕ) : ContractibleSpace ({N n}ᶜ : Set (Sph n)) :=
  contractibleSpace_sphere_compl_singleton _

instance contractibleSpace_compl_S (n : ℕ) : ContractibleSpace ({S n}ᶜ : Set (Sph n)) :=
  contractibleSpace_sphere_compl_singleton _

/-! ### Coordinates -/

/-- a vector whose first `n` coordinates vanish is a multiple of the last basis vector -/
lemma eq_smul_single_last {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1)))
    (h : ∀ j : Fin n, x (Fin.castSucc j) = 0) :
    x = x (Fin.last n) • EuclideanSpace.single (Fin.last n) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp [h j, Fin.castSucc_ne_last]

lemma norm_eq_abs_last {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1)))
    (h : ∀ j : Fin n, x (Fin.castSucc j) = 0) : ‖x‖ = |x (Fin.last n)| := by
  conv_lhs => rw [eq_smul_single_last x h]
  simp [norm_smul]

/-- a point of the sphere whose first `n` coordinates vanish is a pole -/
lemma eq_N_or_eq_S {n : ℕ} (x : Sph n) (h : ∀ j : Fin n, x.1 (Fin.castSucc j) = 0) :
    x = N n ∨ x = S n := by
  have hx : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  rw [norm_eq_abs_last x.1 h] at hx
  rcases abs_eq (zero_le_one' ℝ) |>.1 hx with h1 | h1
  · left
    apply Subtype.ext
    rw [eq_smul_single_last x.1 h, h1, one_smul]
    rfl
  · right
    apply Subtype.ext
    rw [eq_smul_single_last x.1 h, h1, neg_one_smul]
    rfl

/-! ### The projection to the equatorial plane and the inclusion of the equator -/

/-- projection forgetting the last coordinate -/
def proj (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 2)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun x := WithLp.toLp 2 fun j => x (Fin.castSucc j)
  map_add' x y := by ext j; simp
  map_smul' c x := by ext j; simp

@[simp] lemma proj_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 2))) (j : Fin (n + 1)) :
    proj n x j = x (Fin.castSucc j) := rfl

lemma continuous_proj (n : ℕ) : Continuous (proj n) :=
  (proj n).continuous_of_finiteDimensional

/-- inclusion of the equatorial plane, appending a zero last coordinate -/
def incl (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) where
  toFun y := WithLp.toLp 2 (Fin.snoc (fun j => y j) 0)
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.snoc_castSucc, Fin.snoc_last]
  map_smul' c x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.snoc_castSucc, Fin.snoc_last]

@[simp] lemma incl_apply_castSucc {n : ℕ} (y : EuclideanSpace ℝ (Fin (n + 1)))
    (j : Fin (n + 1)) :
    incl n y (Fin.castSucc j) = y j := by
  simp [incl, Fin.snoc_castSucc]

@[simp] lemma incl_apply_last {n : ℕ} (y : EuclideanSpace ℝ (Fin (n + 1))) :
    incl n y (Fin.last (n + 1)) = 0 := by
  simp [incl, Fin.snoc_last]

lemma continuous_incl (n : ℕ) : Continuous (incl n) :=
  (incl n).continuous_of_finiteDimensional

@[simp] lemma proj_incl {n : ℕ} (y : EuclideanSpace ℝ (Fin (n + 1))) :
    proj n (incl n y) = y := by
  ext j
  simp

lemma norm_incl {n : ℕ} (y : EuclideanSpace ℝ (Fin (n + 1))) : ‖incl n y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_castSucc]
  simp

lemma proj_eq_zero_iff {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 2))) :
    proj n x = 0 ↔ ∀ j : Fin (n + 1), x (Fin.castSucc j) = 0 := by
  constructor
  · intro h j
    rw [← proj_apply, h]
    rfl
  · intro h
    ext j
    simp [h j]

lemma proj_N (n : ℕ) : proj n (N (n + 1)).1 = 0 := by
  rw [proj_eq_zero_iff]
  intro j
  simp [Fin.castSucc_ne_last]

lemma proj_S (n : ℕ) : proj n (S (n + 1)).1 = 0 := by
  have h := proj_N n
  rw [N_val] at h
  rw [S_val, map_neg, h, neg_zero]

/-- a point of `Sph (n+1)` is off the poles iff its equatorial projection is nonzero -/
lemma proj_ne_zero_iff {n : ℕ} (x : Sph (n + 1)) :
    proj n x.1 ≠ 0 ↔ x ≠ N (n + 1) ∧ x ≠ S (n + 1) := by
  constructor
  · intro h
    refine ⟨fun hx => h ?_, fun hx => h ?_⟩
    · rw [hx]; exact proj_N n
    · rw [hx]; exact proj_S n
  · rintro ⟨h1, h2⟩ h
    rcases eq_N_or_eq_S x ((proj_eq_zero_iff _).1 h) with h' | h'
    · exact h1 h'
    · exact h2 h'

/-! ### The equator -/

/-- the complement of the two poles -/
abbrev equator (n : ℕ) : Set (Sph (n + 1)) := {N (n + 1)}ᶜ ∩ {S (n + 1)}ᶜ

lemma mem_equator_iff {n : ℕ} (x : Sph (n + 1)) :
    x ∈ equator n ↔ proj n x.1 ≠ 0 := by
  rw [proj_ne_zero_iff]
  simp [equator]

lemma proj_ne_zero {n : ℕ} (x : equator n) : proj n x.1.1 ≠ 0 :=
  (mem_equator_iff x.1).1 x.2

/-- radial projection of a vector with nonzero equatorial part lands in the equator -/
lemma radialProj_mem_equator {n : ℕ} {v : EuclideanSpace ℝ (Fin (n + 2))}
    (hv : proj n v ≠ 0) :
    (⟨radialProj v, radialProj_mem_sphere (fun h => hv (by rw [h, map_zero]))⟩ :
      Sph (n + 1)) ∈ equator n := by
  rw [mem_equator_iff]
  show proj n (‖v‖⁻¹ • v) ≠ 0
  rw [map_smul]
  exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 fun h => hv (by rw [h, map_zero]))) hv

/-- the map from the complement of the poles to the equator -/
def toEquator {n : ℕ} (x : equator n) : Sph n :=
  ⟨radialProj (proj n x.1.1), radialProj_mem_sphere (proj_ne_zero x)⟩

lemma continuous_toEquator (n : ℕ) : Continuous (toEquator (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_radialProj_comp
    ((continuous_proj n).comp (continuous_subtype_val.comp continuous_subtype_val))
    fun x => proj_ne_zero x

/-- the inclusion of the equator -/
def ofEquator {n : ℕ} (y : Sph n) : equator n :=
  ⟨⟨incl n y.1, by
      rw [mem_sphere_zero_iff_norm, norm_incl]
      exact mem_sphere_zero_iff_norm.1 y.2⟩, by
    rw [mem_equator_iff]
    show proj n (incl n y.1) ≠ 0
    rw [proj_incl]
    intro h
    have := mem_sphere_zero_iff_norm.1 y.2
    rw [h, norm_zero] at this
    exact zero_ne_one this⟩

lemma continuous_ofEquator (n : ℕ) : Continuous (ofEquator (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact (continuous_incl n).comp continuous_subtype_val

lemma toEquator_ofEquator {n : ℕ} (y : Sph n) : toEquator (ofEquator y) = y := by
  apply Subtype.ext
  show radialProj (proj n (incl n y.1)) = y.1
  rw [proj_incl]
  exact radialProj_of_norm_eq_one (mem_sphere_zero_iff_norm.1 y.2)

/-- the straight line from `x` to the inclusion of its equatorial projection -/
def line {n : ℕ} (t : ℝ) (x : equator n) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (1 - t) • x.1.1 + t • incl n (radialProj (proj n x.1.1))

lemma proj_line {n : ℕ} (t : ℝ) (x : equator n) :
    proj n (line t x) = ((1 - t) + t * ‖proj n x.1.1‖⁻¹) • proj n x.1.1 := by
  simp only [line, map_add, map_smul, proj_incl, radialProj, smul_smul, add_smul]

lemma proj_line_ne_zero {n : ℕ} (t : I) (x : equator n) : proj n (line (t : ℝ) x) ≠ 0 := by
  rw [proj_line]
  refine smul_ne_zero ?_ (proj_ne_zero x)
  have hpos : 0 < ‖proj n x.1.1‖⁻¹ := inv_pos.2 (norm_pos_iff.2 (proj_ne_zero x))
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  refine ne_of_gt ?_
  rcases eq_or_lt_of_le ht1 with h | h
  · rw [h]; simpa using hpos
  · have := mul_nonneg ht0 hpos.le
    linarith

lemma continuous_line (n : ℕ) : Continuous fun p : I × equator n => line (p.1 : ℝ) p.2 := by
  have h1 : Continuous fun p : I × equator n => p.2.1.1 :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have h2 : Continuous fun p : I × equator n => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  exact ((continuous_const.sub h2).smul h1).add
    (h2.smul ((continuous_incl n).comp (continuous_radialProj_comp ((continuous_proj n).comp h1)
      fun p => proj_ne_zero p.2)))

/-- the deformation of the complement of the poles onto the equator -/
def equatorHomotopy (n : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (equator n))
      ((⟨ofEquator, continuous_ofEquator n⟩ : C(Sph n, equator n)).comp
        ⟨toEquator, continuous_toEquator n⟩) where
  toFun p := ⟨_, radialProj_mem_equator (proj_line_ne_zero p.1 p.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_radialProj_comp (continuous_line n)
      fun p h => proj_line_ne_zero p.1 p.2 (by rw [h, map_zero])
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    show radialProj (line (0 : ℝ) x) = x.1.1
    simp only [line, sub_zero, one_smul, zero_smul, add_zero]
    exact radialProj_of_norm_eq_one (mem_sphere_zero_iff_norm.1 x.1.2)
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    show radialProj (line (1 : ℝ) x) = incl n (radialProj (proj n x.1.1))
    simp only [line, sub_self, zero_smul, one_smul, zero_add]
    apply radialProj_of_norm_eq_one
    rw [norm_incl]
    exact norm_radialProj (proj_ne_zero x)

/-- the complement of the poles in `Sph (n+1)` is homotopy equivalent to the equator `Sph n` -/
def equatorHomotopyEquiv (n : ℕ) :
    ↥(({N (n + 1)}ᶜ : Set (Sph (n + 1))) ∩ {S (n + 1)}ᶜ) ≃ₕ Sph n where
  toFun := ⟨toEquator, continuous_toEquator n⟩
  invFun := ⟨ofEquator, continuous_ofEquator n⟩
  left_inv := ⟨(equatorHomotopy n).symm⟩
  right_inv := by
    have : (⟨toEquator, continuous_toEquator n⟩ : C(equator n, Sph n)).comp
        ⟨ofEquator, continuous_ofEquator n⟩ = ContinuousMap.id _ :=
      ContinuousMap.ext fun y => toEquator_ofEquator y
    rw [this]

@[simp] lemma equatorHomotopyEquiv_apply {n : ℕ} (x : equator n) :
    equatorHomotopyEquiv n x = toEquator x := rfl

@[simp] lemma equatorHomotopyEquiv_symm_apply {n : ℕ} (y : Sph n) :
    (equatorHomotopyEquiv n).symm y = ofEquator y := rfl

/-! ### Path connectedness -/

instance pathConnectedSpace_succ (n : ℕ) : PathConnectedSpace (Sph (n + 1)) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  refine isPathConnected_sphere ?_ 0 zero_le_one
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (by omega : 1 < n + 2)

theorem pathConnectedSpace_of_one_le {n : ℕ} (hn : 1 ≤ n) : PathConnectedSpace (Sph n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  infer_instance

/-! ### The zero sphere -/

lemma eq_N_or_eq_S_zero (x : Sph 0) : x = N 0 ∨ x = S 0 :=
  eq_N_or_eq_S x (fun j => j.elim0)

@[simp] lemma N_zero_apply : (N 0).1 0 = 1 := by
  simp [Fin.last_zero]

@[simp] lemma S_zero_apply : (S 0).1 0 = -1 := by
  simp [Fin.last_zero]

/-- `Sph 0` is the two-point space `{1, -1}` -/
def sphere0Equiv : Sph 0 ≃ Fin 2 where
  toFun x := if 0 < x.1 0 then 0 else 1
  invFun i := if i = 0 then N 0 else S 0
  left_inv x := by
    rcases eq_N_or_eq_S_zero x with rfl | rfl <;> simp
  right_inv i := by
    fin_cases i <;> simp

instance : Finite (Sph 0) := Finite.of_equiv _ sphere0Equiv.symm

instance : DiscreteTopology (Sph 0) := inferInstance

instance : TotallyDisconnectedSpace (Sph 0) := inferInstance

/-- `Sph 0` is homeomorphic to the discrete two-point space -/
def sphere0 : Sph 0 ≃ₜ Fin 2 := sphere0Equiv.toHomeomorphOfDiscrete

/-- `Sph 0` is homeomorphic to the discrete two-point space, in any universe -/
def sphere0ULift : Sph 0 ≃ₜ ULift.{u} (Fin 2) := sphere0.trans Homeomorph.ulift.symm

end Sphere

end PoincareHighDim.SingularPair
