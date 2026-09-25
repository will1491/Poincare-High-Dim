import Submission.Homology.AffineChains

/-!
# Barycentric subdivision

The barycentric subdivision `Sd` and Hatcher's chain homotopy `T` on affine chains of the standard
simplex, with the identities `∂ Sd = Sd ∂` and `∂ T + T ∂ = 1 - Sd` (Hatcher, proof of
Proposition 2.21), their naturality under affine maps, and the induced natural chain map
`S R X : SC R X ⟶ SC R X` on singular chains together with the chain homotopy
`homotopyIdS : Homotopy (𝟙 _) (S R X)`.
-/

open CategoryTheory Limits AlgebraicTopology Convexity

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

open scoped Simplicial in
/-- the `k`-simplices of the singular simplicial set of `X` -/
abbrev Sing (X : TopCat.{u}) (k : ℕ) : Type u := (TopCat.toSSet.obj X) _⦋k⦌

lemma bary_fin_one {n : ℕ} (w : Fin 1 → Δ n) : (fun _ : Fin 1 => bary w) = w := by
  have hw : w = fun _ => w 0 := by
    funext j
    obtain rfl : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt)
    rfl
  rw [hw, bary_const]

namespace AffChain

/-! ### Subdivision and the homotopy on affine chains -/

/-- barycentric subdivision of affine chains -/
def Sd {n : ℕ} : (k : ℕ) → AffChain k n →ₗ[ℤ] AffChain k n
  | 0 => LinearMap.id
  | k + 1 => Finsupp.linearCombination ℤ
      (fun w => coneL (bary w) k (Sd k (bd k (Finsupp.single w 1))))

/-- Hatcher's chain homotopy between the identity and barycentric subdivision -/
def T {n : ℕ} : (k : ℕ) → AffChain k n →ₗ[ℤ] AffChain (k + 1) n
  | 0 => Finsupp.linearCombination ℤ fun w => coneL (bary w) 0 (Finsupp.single w 1)
  | k + 1 => Finsupp.linearCombination ℤ
      (fun w => coneL (bary w) (k + 1) (Finsupp.single w 1 - T k (bd k (Finsupp.single w 1))))

@[simp] lemma Sd_zero {n : ℕ} :
    (Sd 0 : AffChain 0 n →ₗ[ℤ] AffChain 0 n) = LinearMap.id := rfl

lemma Sd_succ_single {n : ℕ} {k : ℕ} (w : Fin (k + 2) → Δ n) (z : ℤ) :
    Sd (k + 1) (Finsupp.single w z) =
      z • coneL (bary w) k (Sd k (bd k (Finsupp.single w 1))) := by
  simp [Sd, Finsupp.linearCombination_single]

lemma T_zero_single {n : ℕ} (w : Fin 1 → Δ n) (z : ℤ) :
    T 0 (Finsupp.single w z) = z • coneL (bary w) 0 (Finsupp.single w 1) := by
  simp [T, Finsupp.linearCombination_single]

lemma T_succ_single {n : ℕ} {k : ℕ} (w : Fin (k + 2) → Δ n) (z : ℤ) :
    T (k + 1) (Finsupp.single w z) =
      z • coneL (bary w) (k + 1) (Finsupp.single w 1 - T k (bd k (Finsupp.single w 1))) := by
  simp [T, Finsupp.linearCombination_single]

/-- `∂ ∘ Sd = Sd ∘ ∂` -/
theorem bd_comp_Sd {n : ℕ} : ∀ k, (bd k).comp (Sd (k + 1) : AffChain (k + 1) n →ₗ[ℤ] _) =
    (Sd k).comp (bd k)
  | 0 => by
    ext w : 2
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Sd_succ_single, one_smul, Sd_zero,
      LinearMap.id_apply, bd_coneL_zero]
    have := LinearMap.congr_fun (eps_comp_bd (n := n)) (Finsupp.single w 1)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
    rw [this, zero_smul, sub_zero]
  | k + 1 => by
    ext w : 2
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Sd_succ_single, one_smul]
    rw [← LinearMap.comp_apply (bd (k + 1)) (coneL _ _), bd_comp_coneL, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.comp_apply,
      ← LinearMap.comp_apply (bd k) (Sd (k + 1)), bd_comp_Sd k, LinearMap.comp_apply,
      ← LinearMap.comp_apply (bd k) (bd (k + 1)), bd_comp_bd, LinearMap.zero_apply, map_zero,
      map_zero, sub_zero]

lemma bd_Sd_succ {n : ℕ} (k : ℕ) (c : AffChain (k + 1) n) :
    bd k (Sd (k + 1) c) = Sd k (bd k c) :=
  LinearMap.congr_fun (bd_comp_Sd k) c

/-- `∂ ∘ T = 0` in degree `0` -/
theorem bd_comp_T_zero {n : ℕ} : (bd 0).comp (T 0 : AffChain 0 n →ₗ[ℤ] _) = 0 := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, T_zero_single, one_smul, bd_coneL_zero,
    eps_single, bary_fin_one, LinearMap.zero_comp, LinearMap.zero_apply, sub_self]

theorem bd_comp_T_succ_of {n : ℕ} (k : ℕ)
    (h : ∀ y : AffChain (k + 1) n, bd k (T k (bd k y)) = bd k y - Sd k (bd k y)) :
    (bd (k + 1)).comp (T (k + 1) : AffChain (k + 1) n →ₗ[ℤ] _) + (T k).comp (bd k) =
      LinearMap.id - Sd (k + 1) := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, T_succ_single, one_smul,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, Sd_succ_single]
  rw [← LinearMap.comp_apply (bd (k + 1)) (coneL _ _), bd_comp_coneL, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.comp_apply, map_sub, h, sub_sub_cancel]
  abel

/-- `∂ ∘ T + T ∘ ∂ = 1 - Sd` in positive degrees -/
theorem bd_comp_T_succ {n : ℕ} : ∀ k,
    (bd (k + 1)).comp (T (k + 1) : AffChain (k + 1) n →ₗ[ℤ] _) + (T k).comp (bd k) =
      LinearMap.id - Sd (k + 1)
  | 0 => bd_comp_T_succ_of 0 fun y => by
      have := LinearMap.congr_fun (bd_comp_T_zero (n := n)) (bd 0 y)
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
      rw [this, Sd_zero, LinearMap.id_apply, sub_self]
  | k + 1 => bd_comp_T_succ_of (k + 1) fun y => by
      have := LinearMap.congr_fun (bd_comp_T_succ k) (bd (k + 1) y)
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.id_apply] at this
      rw [← LinearMap.comp_apply (bd k) (bd (k + 1)), bd_comp_bd, LinearMap.zero_apply,
        map_zero, add_zero] at this
      exact this

lemma bd_T_zero {n : ℕ} (c : AffChain 0 n) : bd (n := n) 0 (T 0 c) = 0 :=
  LinearMap.congr_fun bd_comp_T_zero c

lemma bd_T_succ_add_T_bd {n : ℕ} (k : ℕ) (c : AffChain (k + 1) n) :
    bd (k + 1) (T (k + 1) c) + T k (bd k c) = c - Sd (k + 1) c :=
  LinearMap.congr_fun (bd_comp_T_succ k) c

/-! ### Naturality under affine maps -/

lemma push_affineSimplex_comp_idVerts {m n : ℕ} (u : Fin (m + 1) → Δ n) :
    affineSimplex u ∘ idVerts m = u := by
  funext i; simp

/-- `Sd` commutes with pushforward along affine maps -/
theorem push_comp_Sd {n n' : ℕ} (u : Fin (n + 1) → Δ n') : ∀ k,
    (push (affineSimplex u) k).comp (Sd k) = (Sd k).comp (push (affineSimplex u) k)
  | 0 => by simp
  | k + 1 => by
    ext w : 2
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Sd_succ_single, one_smul, push_single]
    rw [← LinearMap.comp_apply (push _ _) (coneL _ _), push_comp_coneL, LinearMap.comp_apply,
      ← LinearMap.comp_apply (push _ _) (Sd k), push_comp_Sd u k, LinearMap.comp_apply,
      ← LinearMap.comp_apply (push _ _) (bd k), push_comp_bd, LinearMap.comp_apply, push_single,
      affineSimplex_bary]

/-- `T` commutes with pushforward along affine maps -/
theorem push_comp_T {n n' : ℕ} (u : Fin (n + 1) → Δ n') : ∀ k,
    (push (affineSimplex u) (k + 1)).comp (T k) = (T k).comp (push (affineSimplex u) k)
  | 0 => by
    ext w : 2
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, T_zero_single, one_smul, push_single]
    rw [← LinearMap.comp_apply (push _ _) (coneL _ _), push_comp_coneL, LinearMap.comp_apply,
      push_single, affineSimplex_bary]
  | k + 1 => by
    ext w : 2
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, T_succ_single, one_smul, push_single]
    rw [← LinearMap.comp_apply (push _ _) (coneL _ _), push_comp_coneL, LinearMap.comp_apply,
      map_sub, push_single, ← LinearMap.comp_apply (push _ _) (T k), push_comp_T u k,
      LinearMap.comp_apply, ← LinearMap.comp_apply (push _ _) (bd k), push_comp_bd,
      LinearMap.comp_apply, push_single, affineSimplex_bary]

lemma push_Sd {n n' : ℕ} (u : Fin (n + 1) → Δ n') (k : ℕ) (c : AffChain k n) :
    push (affineSimplex u) k (Sd k c) = Sd k (push (affineSimplex u) k c) :=
  LinearMap.congr_fun (push_comp_Sd u k) c

lemma push_T {n n' : ℕ} (u : Fin (n + 1) → Δ n') (k : ℕ) (c : AffChain k n) :
    push (affineSimplex u) (k + 1) (T k c) = T k (push (affineSimplex u) k c) :=
  LinearMap.congr_fun (push_comp_T u k) c

/-- iterated subdivision -/
def SdPow {n : ℕ} (k : ℕ) : ℕ → AffChain k n →ₗ[ℤ] AffChain k n
  | 0 => LinearMap.id
  | j + 1 => (Sd k).comp (SdPow k j)

@[simp] lemma SdPow_zero {n : ℕ} (k : ℕ) :
    (SdPow k 0 : AffChain k n →ₗ[ℤ] _) = LinearMap.id := rfl

lemma SdPow_succ {n : ℕ} (k j : ℕ) :
    (SdPow k (j + 1) : AffChain k n →ₗ[ℤ] _) = (Sd k).comp (SdPow k j) := rfl

lemma SdPow_succ' {n : ℕ} (k j : ℕ) :
    (SdPow k (j + 1) : AffChain k n →ₗ[ℤ] _) = (SdPow k j).comp (Sd k) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [SdPow_succ, ih, ← LinearMap.comp_assoc, ← SdPow_succ, ih]

lemma bd_SdPow_succ {n : ℕ} (k j : ℕ) (c : AffChain (k + 1) n) :
    bd k (SdPow (k + 1) j c) = SdPow k j (bd k c) := by
  induction j generalizing c with
  | zero => rfl
  | succ j ih => rw [SdPow_succ, LinearMap.comp_apply, bd_Sd_succ, ih, SdPow_succ,
      LinearMap.comp_apply]

lemma push_SdPow {n n' : ℕ} (u : Fin (n + 1) → Δ n') (k j : ℕ) (c : AffChain k n) :
    push (affineSimplex u) k (SdPow k j c) = SdPow k j (push (affineSimplex u) k c) := by
  induction j generalizing c with
  | zero => rfl
  | succ j ih => rw [SdPow_succ, LinearMap.comp_apply, push_Sd, ih, SdPow_succ,
      LinearMap.comp_apply]

end AffChain

/-! ### The natural chain map `S` on singular chains -/

variable (R : ModuleCat.{u} ℤ)

open AffChain

lemma toSSetObjEquiv_affSing {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) {k : ℕ}
    (w : Fin (k + 1) → Δ m) :
    X.toSSetObjEquiv _ (affSing σ w) = σ.comp (affineSimplex w) :=
  Equiv.apply_symm_apply _ _

lemma sing_toSSetObjEquiv {X : TopCat.{u}} {k : ℕ} (τ : Sing X k) :
    sing (X.toSSetObjEquiv _ τ) = τ :=
  Equiv.symm_apply_apply _ _

lemma toSSetObjEquiv_toSSet_map_app {X Y : TopCat.{u}} (f : X ⟶ Y) {k : ℕ}
    (τ : Sing X k) :
    Y.toSSetObjEquiv _ ((TopCat.toSSet.map f).app _ τ) = f.hom.comp (X.toSSetObjEquiv _ τ) :=
  rfl

/-- a chain map `SC R X ⟶ SC R X` determined by a natural family of affine chains
`c k : AffChain k k` ("universal chains") -/
def ofUniversal (X : TopCat.{u}) (c : ∀ k, AffChain k k) (k : ℕ) :
    (SC R X).X k ⟶ (SC R X).X k :=
  Sigma.desc fun τ => toChain R (X.toSSetObjEquiv _ τ) k (c k)

@[reassoc]
lemma ι_ofUniversal (X : TopCat.{u}) (c : ∀ k, AffChain k k) (k : ℕ)
    (τ : Sing X k) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ ofUniversal R X c k =
      toChain R (X.toSSetObjEquiv _ τ) k (c k) :=
  Sigma.ι_comp_desc _ _

/-- the subdivision map in degree `k` -/
def SdMap (X : TopCat.{u}) (k : ℕ) : (SC R X).X k ⟶ (SC R X).X k :=
  ofUniversal R X (fun k => Sd k (Finsupp.single (idVerts k) 1)) k

@[reassoc]
lemma ι_SdMap (X : TopCat.{u}) (k : ℕ) (τ : Sing X k) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ SdMap R X k =
      toChain R (X.toSSetObjEquiv _ τ) k (Sd k (Finsupp.single (idVerts k) 1)) :=
  ι_ofUniversal R X _ k τ

lemma toChain_SdMap {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) (k : ℕ) (c : AffChain k m) :
    toChain R σ k c ≫ SdMap R X k = toChain R σ k (Sd k c) := by
  suffices (Preadditive.rightComp R (SdMap R X k)).comp (toChain R σ k) =
      (toChain R σ k).comp (Sd k).toAddMonoidHom from DFunLike.congr_fun this c
  ext w : 2
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, toChain_single, one_smul,
    rightComp_apply_eq, ι_SdMap, toSSetObjEquiv_affSing]
  rw [← toChain_push, push_Sd, push_single, push_affineSimplex_comp_idVerts]
  rfl

/-- the homotopy map in degree `k` -/
def TMap (X : TopCat.{u}) (k : ℕ) : (SC R X).X k ⟶ (SC R X).X (k + 1) :=
  Sigma.desc fun τ =>
    toChain R (X.toSSetObjEquiv _ τ) (k + 1) (T k (Finsupp.single (idVerts k) 1))

@[reassoc]
lemma ι_TMap (X : TopCat.{u}) (k : ℕ) (τ : Sing X k) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ TMap R X k =
      toChain R (X.toSSetObjEquiv _ τ) (k + 1) (T k (Finsupp.single (idVerts k) 1)) :=
  Sigma.ι_comp_desc _ _

lemma toChain_TMap {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) (k : ℕ) (c : AffChain k m) :
    toChain R σ k c ≫ TMap R X k = toChain R σ (k + 1) (T k c) := by
  suffices (Preadditive.rightComp R (TMap R X k)).comp (toChain R σ k) =
      (toChain R σ (k + 1)).comp (T k).toAddMonoidHom from DFunLike.congr_fun this c
  ext w : 2
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, toChain_single, one_smul,
    rightComp_apply_eq, ι_TMap, toSSetObjEquiv_affSing]
  rw [← toChain_push, push_T, push_single, push_affineSimplex_comp_idVerts]
  rfl

/-- the generator `ι τ` as the image of the identity affine chain -/
lemma ι_eq_toChain {X : TopCat.{u}} {k : ℕ} (τ : Sing X k) :
    (TopCat.toSSet.obj X).ιChainComplex τ =
      toChain R (X.toSSetObjEquiv _ τ) k (Finsupp.single (idVerts k) 1) := by
  rw [toChain_single_idVerts, sing_toSSetObjEquiv]

/-- barycentric subdivision as a chain map -/
def S (X : TopCat.{u}) : SC R X ⟶ SC R X where
  f k := SdMap R X k
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    refine SSet.chainComplex_hom_ext fun τ => ?_
    rw [ι_SdMap_assoc, ← toChain_bd, bd_Sd_succ, ι_eq_toChain R τ, ← Category.assoc,
      ← toChain_bd, toChain_SdMap]

@[simp] lemma S_f (X : TopCat.{u}) (k : ℕ) : (S R X).f k = SdMap R X k := rfl

lemma ι_S_f (X : TopCat.{u}) (k : ℕ) (τ : Sing X k) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (S R X).f k =
      toChain R (X.toSSetObjEquiv _ τ) k (Sd k (Finsupp.single (idVerts k) 1)) :=
  ι_SdMap R X k τ

lemma toChain_S_f {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) (k : ℕ) (c : AffChain k m) :
    toChain R σ k c ≫ (S R X).f k = toChain R σ k (Sd k c) :=
  toChain_SdMap R σ k c

/-- naturality of `S` -/
theorem S_natural {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ S R Y =
      S R X ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R := by
  refine HomologicalComplex.hom_ext _ _ fun k => SSet.chainComplex_hom_ext fun τ => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, SSet.ι_chainComplexMap_f_assoc,
    S_f, S_f, ι_SdMap, ι_SdMap_assoc, toChain_map, toSSetObjEquiv_toSSet_map_app]

/-- naturality of `T` -/
theorem TMap_natural {X Y : TopCat.{u}} (f : X ⟶ Y) (k : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) R).f k ≫ TMap R Y k =
      TMap R X k ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f (k + 1) := by
  refine SSet.chainComplex_hom_ext fun τ => ?_
  rw [SSet.ι_chainComplexMap_f_assoc, ι_TMap, ι_TMap_assoc, toChain_map,
    toSSetObjEquiv_toSSet_map_app]

/-- the chain homotopy `𝟙 ≃ S` with components `TMap` -/
def homotopyIdS (X : TopCat.{u}) : Homotopy (𝟙 (SC R X)) (S R X) where
  hom i j := if h : i + 1 = j then TMap R X i ≫ ((SC R X).XIsoOfEq h).hom else 0
  zero i j hij := by
    have : ¬ i + 1 = j := hij
    simp [this]
  comm i := by
    rcases i with _ | i
    · rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id,
        zero_add, HomologicalComplex.id_f, S_f]
      refine SSet.chainComplex_hom_ext fun τ => ?_
      rw [Category.comp_id, Preadditive.comp_add, ι_TMap_assoc, ← toChain_bd, bd_T_zero,
        map_zero, zero_add, ι_SdMap, Sd_zero, LinearMap.id_apply, ι_eq_toChain]
    · rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id,
        HomologicalComplex.id_f, S_f]
      refine SSet.chainComplex_hom_ext fun τ => ?_
      rw [Category.comp_id, Preadditive.comp_add, Preadditive.comp_add, ι_TMap_assoc,
        ← toChain_bd, ι_SdMap, ι_eq_toChain R τ, ← Category.assoc, ← toChain_bd,
        toChain_TMap, ← map_add, ← map_add, add_comm (T _ _), bd_T_succ_add_T_bd,
        sub_add_cancel]

/-- the chain homotopy `S ≃ 𝟙` -/
def homotopySId (X : TopCat.{u}) : Homotopy (S R X) (𝟙 (SC R X)) :=
  (homotopyIdS R X).symm

/-! ### Iterates of `S` -/

/-- the `j`-th iterate of `S` -/
def SPow (X : TopCat.{u}) : ℕ → (SC R X ⟶ SC R X)
  | 0 => 𝟙 _
  | j + 1 => SPow X j ≫ S R X

@[simp] lemma SPow_zero (X : TopCat.{u}) : SPow R X 0 = 𝟙 _ := rfl

lemma SPow_succ (X : TopCat.{u}) (j : ℕ) : SPow R X (j + 1) = SPow R X j ≫ S R X := rfl

lemma toChain_SPow_f {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) (k j : ℕ) (c : AffChain k m) :
    toChain R σ k c ≫ (SPow R X j).f k = toChain R σ k (SdPow k j c) := by
  induction j generalizing c with
  | zero => simp
  | succ j ih => rw [SPow_succ, HomologicalComplex.comp_f, ← Category.assoc, ih, S_f,
      toChain_SdMap, SdPow_succ, LinearMap.comp_apply]

@[reassoc]
lemma ι_SPow_f (X : TopCat.{u}) (k j : ℕ) (τ : Sing X k) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (SPow R X j).f k =
      toChain R (X.toSSetObjEquiv _ τ) k (SdPow k j (Finsupp.single (idVerts k) 1)) := by
  rw [ι_eq_toChain R τ, toChain_SPow_f]

lemma SPow_natural {X Y : TopCat.{u}} (f : X ⟶ Y) (j : ℕ) :
    SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ SPow R Y j =
      SPow R X j ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R := by
  induction j with
  | zero => simp
  | succ j ih => rw [SPow_succ, SPow_succ, ← Category.assoc, ih, Category.assoc, S_natural,
      Category.assoc]

/-! ### Subcomplexes -/

/-- if all simplices of an affine chain `c` are sent into a subcomplex `A`, the singular chain
`toChain R σ k c` comes from `A` -/
lemma toChain_eq_toChainSub {X : TopCat.{u}} (A : (TopCat.toSSet.obj X).Subcomplex) {m : ℕ}
    (σ : C(Δ m, X)) (k : ℕ) (c : AffChain k m)
    (hc : ∀ w ∈ c.support, affSing σ w ∈ A.obj _) :
    toChain R σ k c = toChainSub R A σ k c ≫ (SSet.chainComplexMap A.ι R).f k :=
  (toChainSub_ι R A σ k c hc).symm

end PoincareHighDim.SingularPair
