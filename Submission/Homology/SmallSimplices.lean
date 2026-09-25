import Submission.Homology.SingularSubcomplex
import Submission.Homology.DiameterBound

/-!
# Small simplices (Hatcher, Proposition 2.21)

For a family `U : ι → Set X` whose interiors cover `X`, the inclusion of the subcomplex of
`U`-small singular chains `C^U(X) := ((small X U : SSet).chainComplex R)` into the singular
chains `C(X)` is a chain homotopy equivalence, hence a quasi-isomorphism.

Following Hatcher (proof of Prop. 2.21), we use the barycentric subdivision `S` with its chain
homotopy `T` (`𝟙 ≃ S`, from `Submission.Homology.Subdivision`), the iterated homotopies
`D k = ∑_{i < k} S^i T` between `S^k` and `𝟙` (`Dk`), the minimal subdivision index
`mIdx σ` (the least `k` with `σ` `k`-small, from the Lebesgue number argument in
`Submission.Homology.DiameterBound`), the homotopy `D σ := D_{m(σ)} σ` (`Dmap`), and Hatcher's
chain map `ρ := 𝟙 - ∂D - D∂` (`ρbig`), which takes values in the small chains (`ρ`).  Then
`ι ≫ ρ = 𝟙` (`smallChainMap_comp_ρ`) and `ρ ≫ ι ≃ 𝟙` via `D` (`homotopyρ`), giving the
homotopy equivalence `smallHomotopyEquiv` and the quasi-isomorphism `quasiIso_smallChainMap`.
-/

open CategoryTheory Limits AlgebraicTopology Convexity
open scoped Simplicial

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

open AffChain

variable (R : ModuleCat.{u} ℤ) (X : TopCat.{u})

/-! ### The identities `∂T + T∂ = 1 - S` in degreewise form -/

lemma TMap_d_zero : TMap R X 0 ≫ (SC R X).d 1 0 + (S R X).f 0 = 𝟙 _ := by
  have h := (homotopyIdS R X).comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at h
  simp only [homotopyIdS, dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.comp_id, zero_add, HomologicalComplex.id_f] at h
  exact h.symm

lemma d_TMap_add_TMap_d (j : ℕ) :
    (SC R X).d (j + 1) j ≫ TMap R X j + TMap R X (j + 1) ≫ (SC R X).d (j + 2) (j + 1) +
      (S R X).f (j + 1) = 𝟙 _ := by
  have h := (homotopyIdS R X).comm (j + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  simp only [homotopyIdS, dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.comp_id, HomologicalComplex.id_f] at h
  exact h.symm

/-! ### The iterated homotopies `D k = ∑_{i < k} T S^i` -/

/-- the homotopy `D k` between `S^k` and the identity, in degree `j` -/
def Dk (k j : ℕ) : (SC R X).X j ⟶ (SC R X).X (j + 1) :=
  ∑ i ∈ Finset.range k, (SPow R X i).f j ≫ TMap R X j

@[simp] lemma Dk_zero (j : ℕ) : Dk R X 0 j = 0 := by simp [Dk]

lemma Dk_succ (k j : ℕ) : Dk R X (k + 1) j = Dk R X k j + (SPow R X k).f j ≫ TMap R X j := by
  simp [Dk, Finset.sum_range_succ]

lemma Dk_sub_Dk {k k' : ℕ} (h : k' ≤ k) (j : ℕ) :
    Dk R X k j - Dk R X k' j = ∑ i ∈ Finset.Ico k' k, (SPow R X i).f j ≫ TMap R X j := by
  rw [sub_eq_iff_eq_add', Dk, Dk, Finset.sum_range_add_sum_Ico _ h]

lemma Dk_d_zero (k : ℕ) : Dk R X k 0 ≫ (SC R X).d 1 0 + (SPow R X k).f 0 = 𝟙 _ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Dk_succ, Preadditive.add_comp, SPow_succ, HomologicalComplex.comp_f, Category.assoc,
      add_assoc, ← Preadditive.comp_add, TMap_d_zero, Category.comp_id, ih]

lemma d_Dk_add_Dk_d (k j : ℕ) :
    (SC R X).d (j + 1) j ≫ Dk R X k j + Dk R X k (j + 1) ≫ (SC R X).d (j + 2) (j + 1) +
      (SPow R X k).f (j + 1) = 𝟙 _ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Dk_succ, Dk_succ, Preadditive.add_comp, Preadditive.comp_add, SPow_succ,
      HomologicalComplex.comp_f, Category.assoc,
      ← (SPow R X k).comm_assoc (j + 1) j]
    have key : (SPow R X k).f (j + 1) ≫ ((SC R X).d (j + 1) j ≫ TMap R X j +
        TMap R X (j + 1) ≫ (SC R X).d (j + 2) (j + 1) + (S R X).f (j + 1)) =
        (SPow R X k).f (j + 1) := by
      rw [d_TMap_add_TMap_d, Category.comp_id]
    simp only [Preadditive.comp_add] at key
    calc _ = ((SC R X).d (j + 1) j ≫ Dk R X k j +
          Dk R X k (j + 1) ≫ (SC R X).d (j + 2) (j + 1) +
          (SPow R X k).f (j + 1)) - (SPow R X k).f (j + 1) +
          ((SPow R X k).f (j + 1) ≫ (SC R X).d (j + 1) j ≫ TMap R X j +
            (SPow R X k).f (j + 1) ≫ TMap R X (j + 1) ≫ (SC R X).d (j + 2) (j + 1) +
            (SPow R X k).f (j + 1) ≫ (S R X).f (j + 1)) := by abel
      _ = 𝟙 _ := by rw [ih, key, sub_add_cancel]


/-! ### The minimal subdivision index of a singular simplex -/

section cover

variable {X} {ι : Type*} (U : ι → Set X)

/-- the inclusion of the `U`-small chains, with codomain in the reducible form `SC R X` -/
abbrev smallInc :
    ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R ⟶ SC R X :=
  SSet.chainComplexMap (small X U).ι R

instance (n : ℕ) : Mono ((smallInc R U).f n) :=
  inferInstanceAs (Mono ((SSet.chainComplexMap (small X U).pair.hom R).f n))

@[reassoc]
lemma ι_smallInc_f {n : ℕ}
    (σ : ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) _⦋n⦌) :
    ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).ιChainComplex σ ≫
      (smallInc R U).f n = (TopCat.toSSet.obj X).ιChainComplex σ.1 :=
  SSet.ι_chainComplexMap_f _ _ (small X U).ι R σ

variable (hU : ⋃ i, interior (U i) = Set.univ)

open Classical in
/-- the least `k` such that the singular simplex `τ` is `k`-small for the cover `U` -/
def mIdx {m : ℕ} (τ : Sing X m) : ℕ :=
  Nat.find (exists_isSmall hU (X.toSSetObjEquiv _ τ))

lemma isSmall_mIdx {m : ℕ} (τ : Sing X m) :
    IsSmall U (X.toSSetObjEquiv _ τ) (mIdx U hU τ) := by
  classical exact Nat.find_spec (exists_isSmall hU (X.toSSetObjEquiv _ τ))

lemma mIdx_le {m : ℕ} (τ : Sing X m) {k : ℕ} (h : IsSmall U (X.toSSetObjEquiv _ τ) k) :
    mIdx U hU τ ≤ k := by
  classical exact Nat.find_min' (exists_isSmall hU (X.toSSetObjEquiv _ τ)) h

lemma mIdx_δ_le {m : ℕ} (τ : Sing X (m + 1)) (i : Fin (m + 2)) :
    mIdx U hU ((TopCat.toSSet.obj X).δ i τ) ≤ mIdx U hU τ :=
  mIdx_le U hU _ ((isSmall_mIdx U hU τ).δ i)

lemma isSmall_zero_of_mem_small {m : ℕ} {τ : Sing X m} (hτ : τ ∈ (small X U).obj _) :
    IsSmall U (X.toSSetObjEquiv _ τ) 0 := by
  obtain ⟨i, hi⟩ := (mem_small_iff U τ).1 hτ
  intro s _
  exact ⟨i, (Set.image_subset_range _ _).trans hi⟩

lemma mIdx_eq_zero_of_mem_small {m : ℕ} {τ : Sing X m} (hτ : τ ∈ (small X U).obj _) :
    mIdx U hU τ = 0 :=
  Nat.le_zero.1 (mIdx_le U hU τ (isSmall_zero_of_mem_small U hτ))

lemma δ_mem_small {m : ℕ} {τ : Sing X (m + 1)} (hτ : τ ∈ (small X U).obj _)
    (i : Fin (m + 2)) :
    (TopCat.toSSet.obj X).δ i τ ∈ (small X U).obj _ :=
  (small X U).map _ hτ

/-! ### Hatcher's homotopy `D` with variable iterate -/

/-- the homotopy `D σ := D_{m(σ)} σ` in degree `j` -/
def Dmap (j : ℕ) : (SC R X).X j ⟶ (SC R X).X (j + 1) :=
  Sigma.desc fun τ => (TopCat.toSSet.obj X).ιChainComplex τ ≫ Dk R X (mIdx U hU τ) j

@[reassoc]
lemma ι_Dmap {j : ℕ} (τ : Sing X j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ Dmap R U hU j =
      (TopCat.toSSet.obj X).ιChainComplex τ ≫ Dk R X (mIdx U hU τ) j :=
  Sigma.ι_comp_desc _ _

lemma ι_d_Dmap {j : ℕ} (τ : Sing X (j + 1)) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (SC R X).d (j + 1) j ≫ Dmap R U hU j =
      ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) • ((TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).δ i τ) ≫
          Dk R X (mIdx U hU ((TopCat.toSSet.obj X).δ i τ)) j) := by
  rw [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, ι_Dmap]

/-- the family of maps underlying the null-homotopic chain map `∂D + D∂` -/
def Dhom (i j : ℕ) : (SC R X).X i ⟶ (SC R X).X j :=
  if h : i + 1 = j then Dmap R U hU i ≫ ((SC R X).XIsoOfEq h).hom else 0

lemma Dhom_succ (i : ℕ) : Dhom R U hU i (i + 1) = Dmap R U hU i := by
  simp [Dhom]

/-- the chain map `∂D + D∂` -/
abbrev Nmap : SC R X ⟶ SC R X := Homotopy.nullHomotopicMap (Dhom R U hU)

lemma Nmap_f_zero : (Nmap R U hU).f 0 = Dmap R U hU 0 ≫ (SC R X).d 1 0 := by
  change dNext 0 (Dhom R U hU) + prevD 0 (Dhom R U hU) = _
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, Dhom_succ, zero_add]

lemma Nmap_f_succ (j : ℕ) : (Nmap R U hU).f (j + 1) =
    (SC R X).d (j + 1) j ≫ Dmap R U hU j +
      Dmap R U hU (j + 1) ≫ (SC R X).d (j + 2) (j + 1) := by
  change dNext (j + 1) (Dhom R U hU) + prevD (j + 1) (Dhom R U hU) = _
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, Dhom_succ, Dhom_succ]

/-- the chain map `ρ` viewed as a map `C(X) ⟶ C(X)`: `1 - ∂D - D∂` -/
abbrev ρbig : SC R X ⟶ SC R X := 𝟙 _ - Nmap R U hU

lemma ι_ρbig_zero (τ : Sing X 0) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f 0 =
      (TopCat.toSSet.obj X).ιChainComplex τ ≫ (SPow R X (mIdx U hU τ)).f 0 := by
  have hD : Dk R X (mIdx U hU τ) 0 ≫ (SC R X).d 1 0 =
      𝟙 _ - (SPow R X (mIdx U hU τ)).f 0 := by
    rw [← Dk_d_zero R X (mIdx U hU τ)]; abel
  rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, Nmap_f_zero, Preadditive.comp_sub,
    Category.comp_id, ι_Dmap_assoc, hD, Preadditive.comp_sub, Category.comp_id, sub_sub_cancel]

lemma ι_ρbig_succ {j : ℕ} (τ : Sing X (j + 1)) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f (j + 1) =
      (TopCat.toSSet.obj X).ιChainComplex τ ≫ (SPow R X (mIdx U hU τ)).f (j + 1) +
      ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) • ((TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).δ i τ) ≫
          (Dk R X (mIdx U hU τ) j - Dk R X (mIdx U hU ((TopCat.toSSet.obj X).δ i τ)) j)) := by
  have hD : Dk R X (mIdx U hU τ) (j + 1) ≫ (SC R X).d (j + 2) (j + 1) =
      𝟙 _ - (SC R X).d (j + 1) j ≫ Dk R X (mIdx U hU τ) j -
        (SPow R X (mIdx U hU τ)).f (j + 1) := by
    rw [← d_Dk_add_Dk_d R X (mIdx U hU τ) j]; abel
  have h2 : (TopCat.toSSet.obj X).ιChainComplex τ ≫ Dmap R U hU (j + 1) ≫
      (SC R X).d (j + 2) (j + 1) =
      (TopCat.toSSet.obj X).ιChainComplex τ -
        ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) • ((TopCat.toSSet.obj X).ιChainComplex
          ((TopCat.toSSet.obj X).δ i τ) ≫ Dk R X (mIdx U hU τ) j) -
        (TopCat.toSSet.obj X).ιChainComplex τ ≫ (SPow R X (mIdx U hU τ)).f (j + 1) := by
    rw [ι_Dmap_assoc, hD, Preadditive.comp_sub, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp]
  rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, Nmap_f_succ, Preadditive.comp_sub,
    Category.comp_id, Preadditive.comp_add, ι_d_Dmap, h2]
  simp only [Preadditive.comp_sub, smul_sub, Finset.sum_sub_distrib]
  abel

lemma ι_ρbig_of_mem_small {j : ℕ} {τ : Sing X j} (hτ : τ ∈ (small X U).obj _) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f j =
      (TopCat.toSSet.obj X).ιChainComplex τ := by
  cases j with
  | zero =>
    rw [ι_ρbig_zero, mIdx_eq_zero_of_mem_small U hU hτ, SPow_zero, HomologicalComplex.id_f,
      Category.comp_id]
  | succ j =>
    rw [ι_ρbig_succ, mIdx_eq_zero_of_mem_small U hU hτ, SPow_zero, HomologicalComplex.id_f,
      Category.comp_id]
    simp only [mIdx_eq_zero_of_mem_small U hU (δ_mem_small U hτ _), sub_self, Limits.comp_zero,
      smul_zero, Finset.sum_const_zero, add_zero]

/-! ### Factorisation through the small chains -/

/-- the morphisms `R ⟶ C_j(X)` that come from the `U`-small chains -/
def smallRange (j : ℕ) : AddSubgroup (R ⟶ (SC R X).X j) :=
  (Preadditive.rightComp R ((smallInc R U).f j)).range

lemma mem_smallRange_iff {j : ℕ} (f : R ⟶ (SC R X).X j) :
    f ∈ smallRange R U j ↔
      ∃ c : R ⟶
        (((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R).X j,
        c ≫ (smallInc R U).f j = f :=
  AddMonoidHom.mem_range

lemma ι_SPow_mem_smallRange {m : ℕ} (τ : Sing X m) {k : ℕ}
    (h : IsSmall U (X.toSSetObjEquiv _ τ) k) {j : ℕ} (hj : k ≤ j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (SPow R X j).f m ∈ smallRange R U m := by
  rw [mem_smallRange_iff, ← sing_toSSetObjEquiv τ,
    h.ι_SPow_f_eq R hj (small X U) (singSub_le_small U)]
  exact ⟨_, rfl⟩

lemma ι_SPow_TMap_mem_smallRange {m : ℕ} (τ : Sing X m) {k : ℕ}
    (h : IsSmall U (X.toSSetObjEquiv _ τ) k) {j : ℕ} (hj : k ≤ j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (SPow R X j).f m ≫ TMap R X m ∈
      smallRange R U (m + 1) := by
  rw [mem_smallRange_iff, ← sing_toSSetObjEquiv τ,
    h.ι_SPow_f_TMap_eq R hj (small X U) (singSub_le_small U)]
  exact ⟨_, rfl⟩

lemma ι_ρbig_mem_smallRange {j : ℕ} (τ : Sing X j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f j ∈ smallRange R U j := by
  cases j with
  | zero =>
    rw [ι_ρbig_zero]
    exact ι_SPow_mem_smallRange R U τ (isSmall_mIdx U hU τ) le_rfl
  | succ j =>
    rw [ι_ρbig_succ]
    refine add_mem (ι_SPow_mem_smallRange R U τ (isSmall_mIdx U hU τ) le_rfl)
      (sum_mem fun i _ => zsmul_mem ?_ _)
    rw [Dk_sub_Dk R X (mIdx_δ_le U hU τ i), Preadditive.comp_sum]
    refine sum_mem fun i' hi' => ?_
    exact ι_SPow_TMap_mem_smallRange R U _ (isSmall_mIdx U hU _) (Finset.mem_Ico.1 hi').1

/-! ### The chain map `ρ` -/

/-- the components of Hatcher's `ρ : C(X) ⟶ C^U(X)` -/
def ρf (j : ℕ) :
    (SC R X).X j ⟶
      (((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R).X j :=
  Sigma.desc fun τ => ((mem_smallRange_iff R U _).1 (ι_ρbig_mem_smallRange R U hU τ)).choose

lemma ι_ρf_comp {j : ℕ} (τ : Sing X j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ ρf R U hU j ≫ (smallInc R U).f j =
      (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f j := by
  rw [← Category.assoc]
  erw [Sigma.ι_comp_desc]
  exact ((mem_smallRange_iff R U _).1 (ι_ρbig_mem_smallRange R U hU τ)).choose_spec

lemma ρf_comp_smallChainMap_f (j : ℕ) :
    ρf R U hU j ≫ (smallInc R U).f j = (ρbig R U hU).f j :=
  SSet.chainComplex_hom_ext fun τ => ι_ρf_comp R U hU τ

/-- Hatcher's chain map `ρ : C(X) ⟶ C^U(X)`, a chain-homotopy inverse of the inclusion -/
def ρ : SC R X ⟶ ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R where
  f j := ρf R U hU j
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [← cancel_mono ((smallInc R U).f j), Category.assoc, Category.assoc,
      ← (smallInc R U).comm (j + 1) j, ← Category.assoc, ρf_comp_smallChainMap_f,
      ρf_comp_smallChainMap_f, (ρbig R U hU).comm]

@[simp] lemma ρ_f (j : ℕ) : (ρ R U hU).f j = ρf R U hU j := rfl

theorem ρ_comp_smallChainMap : ρ R U hU ≫ smallInc R U = ρbig R U hU :=
  HomologicalComplex.hom_ext _ _ fun j => ρf_comp_smallChainMap_f R U hU j

theorem smallChainMap_comp_ρ : smallInc R U ≫ ρ R U hU = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [← cancel_mono ((smallInc R U).f j), Category.assoc, Category.assoc, ρ_f,
    ρf_comp_smallChainMap_f, Category.comp_id, ι_smallInc_f_assoc,
    ι_ρbig_of_mem_small R U hU σ.2, ι_smallInc_f]

/-- the chain homotopy `ρ ≫ ι ≃ 𝟙` with components `-D` -/
def homotopyρ : Homotopy (ρ R U hU ≫ smallInc R U) (𝟙 (SC R X)) where
  hom := -Dhom R U hU
  zero i j hij := by
    have : ¬ i + 1 = j := hij
    simp [Dhom, this]
  comm i := by
    rw [ρ_comp_smallChainMap, map_neg, map_neg, HomologicalComplex.sub_f_apply,
      HomologicalComplex.id_f]
    change 𝟙 _ - (dNext i (Dhom R U hU) + prevD i (Dhom R U hU)) = _
    abel

/-- the inclusion of the `U`-small chains is a chain homotopy equivalence (Hatcher, Prop. 2.21) -/
def smallHomotopyEquiv :
    HomotopyEquiv (((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R)
      (SC R X) where
  hom := smallInc R U
  inv := ρ R U hU
  homotopyHomInvId := Homotopy.ofEq (smallChainMap_comp_ρ R U hU)
  homotopyInvHomId := homotopyρ R U hU

@[simp] lemma smallHomotopyEquiv_hom : (smallHomotopyEquiv R U hU).hom = smallInc R U := rfl

include hU in
/-- **Hatcher, Proposition 2.21**: for a family `U` whose interiors cover `X`, the inclusion of
the `U`-small singular chains is a quasi-isomorphism. -/
theorem quasiIso_smallChainMap : QuasiIso (SSet.chainComplexMap (small X U).ι R) :=
  (smallHomotopyEquiv R U hU).quasiIso_hom

include hU in
/-- the same statement for `smallChainMap X R U` (codomain written as `C R X`) -/
theorem quasiIso_smallChainMap' : QuasiIso (smallChainMap X R U) :=
  quasiIso_smallChainMap R U hU

include hU in
theorem quasiIsoAt_smallChainMap (n : ℕ) :
    QuasiIsoAt (SSet.chainComplexMap (small X U).ι R) n :=
  (smallHomotopyEquiv R U hU).quasiIsoAt_hom n

include hU in
theorem isIso_homologyMap_smallChainMap (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (SSet.chainComplexMap (small X U).ι R) n) :=
  (quasiIsoAt_iff_isIso_homologyMap _ n).1 (quasiIsoAt_smallChainMap R U hU n)

include hU in
theorem isIso_homologyMap_small (n : ℕ) :
    IsIso (SSet.homologyMap (small X U).ι R n) :=
  isIso_homologyMap_smallChainMap R U hU n

end cover

end PoincareHighDim.SingularPair
