import Submission.Homology.SingularPair

/-!
# The Mayer–Vietoris short exact sequence for subcomplexes

For a simplicial set `K` and two subcomplexes `A B : K.Subcomplex`, the square

```
A ⊓ B ⟶ A
  |       |
  v       v
  B   ⟶ A ⊔ B
```

is bicartesian in the lattice of subcomplexes, hence a pushout of simplicial sets
(`SSet.Subcomplex.BicartSq.isPushout`).  Applying the simplicial chain complex functor with
coefficients `R : ModuleCat ℤ` gives, degreewise, a pushout of coproducts of copies of `R`
(`sigmaConst.obj R` preserves colimits), hence a pushout of chain complexes
(`isPushout`), and therefore the short exact sequence of chain complexes

`0 ⟶ C(A ⊓ B) ⟶ C(A) ⊞ C(B) ⟶ C(A ⊔ B) ⟶ 0`

(`mvShortComplex`, `mvShortComplex_shortExact`), with the sign convention of
`CommSq.shortComplex`: the first map is `biprod.lift ι₁ (-ι₂)` and the second is
`biprod.desc j₁ j₂`.

From it we extract the Mayer–Vietoris long exact sequence in homology, both in its raw form
(`mvδ`, `mv_exact₁`, `mv_exact₂`, `mv_exact₃`, with middle term `(C(A) ⊞ C(B)).homology n`)
and in the packaged form with middle term `H_n(A) ⊞ H_n(B)` (`mvLift`, `mvDesc`,
`mv_exact₁'`, `mv_exact₂'`, `mv_exact₃'`).

Finally, the pushout square gives excision at the chain level: the inclusion `B ↪ A ⊔ B`
induces an isomorphism `C(B)/C(A ⊓ B) ≅ C(A ⊔ B)/C(A)` of relative chain complexes
(`cokerIso`), i.e. the morphism of pairs `excisionPairMap : (B, A ⊓ B) ⟶ (A ⊔ B, A)` induces
isomorphisms in relative homology (`isIso_homologyMap_excisionPairMap`).

Everything is universe polymorphic (`SSet.{u}`, `ModuleCat.{u} ℤ`).
-/

open CategoryTheory Limits Simplicial Opposite HomologicalComplex

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

/-! ### Cokernels of parallel legs of a pushout square agree -/

section CokerIso

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/-- In a pushout square `t, l, r, b`, the bottom map `b` induces an isomorphism from the
cokernel of `l` to the cokernel of `r`. -/
def pushoutCokernelIso (h : IsPushout t l r b)
    {cl : CokernelCofork l} (hl : IsColimit cl)
    {cr : CokernelCofork r} (hr : IsColimit cr) :
    cl.pt ≅ cr.pt where
  hom := Cofork.IsColimit.desc hl (b ≫ cr.π) (by
    rw [← Category.assoc, ← h.w, Category.assoc, cr.condition, comp_zero, zero_comp])
  inv := Cofork.IsColimit.desc hr (h.desc 0 cl.π (by simp [cl.condition]))
    (by simp [zero_comp])
  hom_inv_id := by
    apply Cofork.IsColimit.hom_ext hl
    simp
  inv_hom_id := by
    apply Cofork.IsColimit.hom_ext hr
    apply h.hom_ext
    · simp
    · simp

@[reassoc (attr := simp)]
lemma π_pushoutCokernelIso_hom (h : IsPushout t l r b)
    {cl : CokernelCofork l} (hl : IsColimit cl)
    {cr : CokernelCofork r} (hr : IsColimit cr) :
    cl.π ≫ (pushoutCokernelIso h hl hr).hom = b ≫ cr.π := by
  simp [pushoutCokernelIso]

@[reassoc (attr := simp)]
lemma π_pushoutCokernelIso_inv (h : IsPushout t l r b)
    {cl : CokernelCofork l} (hl : IsColimit cl)
    {cr : CokernelCofork r} (hr : IsColimit cr) :
    b ≫ cr.π ≫ (pushoutCokernelIso h hl hr).inv = cl.π := by
  simp [pushoutCokernelIso]

end CokerIso

/-! ### The pushout square of chain complexes -/

variable {K : SSet.{u}} (A B : K.Subcomplex) (R : ModuleCat.{u} ℤ)

lemma bicartSq : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) where
  sup_eq := rfl
  inf_eq := rfl

lemma isPushout_sset :
    IsPushout (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
      (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
      (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
      (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) :=
  (bicartSq A B).isPushout

/-- `C(A ⊓ B) ⟶ C(A)` -/
abbrev ι₁ :
    ((A ⊓ B : K.Subcomplex) : SSet.{u}).chainComplex R ⟶ (A : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) R

/-- `C(A ⊓ B) ⟶ C(B)` -/
abbrev ι₂ :
    ((A ⊓ B : K.Subcomplex) : SSet.{u}).chainComplex R ⟶ (B : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) R

/-- `C(A) ⟶ C(A ⊔ B)` -/
abbrev j₁ :
    (A : SSet.{u}).chainComplex R ⟶ ((A ⊔ B : K.Subcomplex) : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)) R

/-- `C(B) ⟶ C(A ⊔ B)` -/
abbrev j₂ :
    (B : SSet.{u}).chainComplex R ⟶ ((A ⊔ B : K.Subcomplex) : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) R

/-- degreewise, the square of chains is a pushout (image of the pushout of `n`-simplices
under `sigmaConst.obj R`) -/
lemma isPushout_X (n : ℕ) :
    IsPushout ((ι₁ A B R).f n) ((ι₂ A B R).f n) ((j₁ A B R).f n) ((j₂ A B R).f n) :=
  ((isPushout_sset A B).map ((evaluation _ _).obj (op ⦋n⦌))).map (sigmaConst.obj R)

lemma ι₁_j₁ : ι₁ A B R ≫ j₁ A B R = ι₂ A B R ≫ j₂ A B R := by
  simp only [ι₁, j₁, ι₂, j₂, ← Functor.map_comp]
  rfl

/-- the square of chain complexes is a pushout -/
lemma isPushout : IsPushout (ι₁ A B R) (ι₂ A B R) (j₁ A B R) (j₂ A B R) where
  w := ι₁_j₁ A B R
  isColimit' := ⟨isColimitOfEval _ _ (fun n ↦
    (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (isPushout_X A B R n).isColimit)⟩

instance : Mono (ι₁ A B R) :=
  inferInstanceAs (Mono (SSet.chainComplexMap
    (SSetPair.of (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))).hom R))

instance : Mono (ι₂ A B R) :=
  inferInstanceAs (Mono (SSet.chainComplexMap
    (SSetPair.of (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))).hom R))

instance : Mono (j₁ A B R) :=
  inferInstanceAs (Mono (SSet.chainComplexMap
    (SSetPair.of (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))).hom R))

instance : Mono (j₂ A B R) :=
  inferInstanceAs (Mono (SSet.chainComplexMap
    (SSetPair.of (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))).hom R))

/-! ### The Mayer–Vietoris short exact sequence -/

@[reassoc (attr := simp)]
lemma lift_desc :
    biprod.lift (ι₁ A B R) (-(ι₂ A B R)) ≫ biprod.desc (j₁ A B R) (j₂ A B R) = 0 := by
  simp [ι₁_j₁]

/-- the Mayer–Vietoris short complex `C(A ⊓ B) ⟶ C(A) ⊞ C(B) ⟶ C(A ⊔ B)` -/
def mvShortComplex : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (biprod.lift (ι₁ A B R) (-(ι₂ A B R)))
    (biprod.desc (j₁ A B R) (j₂ A B R)) (lift_desc A B R)

lemma mvShortComplex_eq : mvShortComplex A B R = (isPushout A B R).shortComplex := rfl

@[simp] lemma mvShortComplex_X₁ :
    (mvShortComplex A B R).X₁ = ((A ⊓ B : K.Subcomplex) : SSet.{u}).chainComplex R := rfl

@[simp] lemma mvShortComplex_X₂ :
    (mvShortComplex A B R).X₂ =
      ((A : SSet.{u}).chainComplex R ⊞ (B : SSet.{u}).chainComplex R) := rfl

@[simp] lemma mvShortComplex_X₃ :
    (mvShortComplex A B R).X₃ = ((A ⊔ B : K.Subcomplex) : SSet.{u}).chainComplex R := rfl

@[simp] lemma mvShortComplex_f :
    (mvShortComplex A B R).f = biprod.lift (ι₁ A B R) (-(ι₂ A B R)) := rfl

@[simp] lemma mvShortComplex_g :
    (mvShortComplex A B R).g = biprod.desc (j₁ A B R) (j₂ A B R) := rfl

/-- the Mayer–Vietoris short complex is short exact -/
theorem mvShortComplex_shortExact : (mvShortComplex A B R).ShortExact where
  exact := (isPushout A B R).exact_shortComplex
  mono_f := by
    dsimp [mvShortComplex]
    exact mono_of_mono_fac (biprod.lift_fst _ _)
  epi_g := (isPushout A B R).epi_shortComplex_g

/-! ### The long exact sequence, raw form -/

/-- the Mayer–Vietoris connecting morphism `H_{n+1}(A ⊔ B) ⟶ H_n(A ⊓ B)` -/
def mvδ (n : ℕ) :
    ((A ⊔ B : K.Subcomplex) : SSet.{u}).homology R (n + 1) ⟶
      ((A ⊓ B : K.Subcomplex) : SSet.{u}).homology R n :=
  (mvShortComplex_shortExact A B R).δ (n + 1) n rfl

@[reassoc (attr := simp)]
lemma mvδ_comp (n : ℕ) :
    mvδ A B R n ≫ homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n = 0 :=
  (mvShortComplex_shortExact A B R).δ_comp (n + 1) n rfl

@[reassoc (attr := simp)]
lemma comp_mvδ (n : ℕ) :
    homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) (n + 1) ≫ mvδ A B R n = 0 :=
  (mvShortComplex_shortExact A B R).comp_δ (n + 1) n rfl

lemma homologyMap_lift_desc (n : ℕ) :
    homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n ≫
      homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) n = 0 := by
  rw [← homologyMap_comp, lift_desc, homologyMap_zero]

/-- `H_{n+1}(A ⊔ B) ⟶ H_n(A ⊓ B) ⟶ H_n(C(A) ⊞ C(B))` is exact -/
theorem mv_exact₁ (n : ℕ) :
    (ShortComplex.mk (mvδ A B R n) (homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n)
      (mvδ_comp A B R n)).Exact :=
  (mvShortComplex_shortExact A B R).homology_exact₁ (n + 1) n rfl

/-- `H_n(A ⊓ B) ⟶ H_n(C(A) ⊞ C(B)) ⟶ H_n(A ⊔ B)` is exact -/
theorem mv_exact₂ (n : ℕ) :
    (ShortComplex.mk (homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n)
      (homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) n)
      (homologyMap_lift_desc A B R n)).Exact :=
  (mvShortComplex_shortExact A B R).homology_exact₂ n

/-- `H_{n+1}(C(A) ⊞ C(B)) ⟶ H_{n+1}(A ⊔ B) ⟶ H_n(A ⊓ B)` is exact -/
theorem mv_exact₃ (n : ℕ) :
    (ShortComplex.mk (homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) (n + 1)) (mvδ A B R n)
      (comp_mvδ A B R n)).Exact :=
  (mvShortComplex_shortExact A B R).homology_exact₃ (n + 1) n rfl

/-! ### The long exact sequence with `H_n(A) ⊞ H_n(B)` -/

/-- homology of a biproduct of chain complexes is the biproduct of the homologies -/
def homologyBiprodIso (n : ℕ) :
    ((A : SSet.{u}).chainComplex R ⊞ (B : SSet.{u}).chainComplex R).homology n ≅
      ((A : SSet.{u}).homology R n ⊞ (B : SSet.{u}).homology R n) where
  hom := biprod.lift (homologyMap biprod.fst n) (homologyMap biprod.snd n)
  inv := biprod.desc (homologyMap biprod.inl n) (homologyMap biprod.inr n)
  hom_inv_id := by
    rw [biprod.lift_desc, ← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add,
      biprod.total, homologyMap_id]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [← homologyMap_comp]

/-- `H_n(A ⊓ B) ⟶ H_n(A) ⊞ H_n(B)`, `x ↦ (x, -x)` -/
def mvLift (n : ℕ) :
    ((A ⊓ B : K.Subcomplex) : SSet.{u}).homology R n ⟶
      ((A : SSet.{u}).homology R n ⊞ (B : SSet.{u}).homology R n) :=
  biprod.lift (SSet.homologyMap (SSet.Subcomplex.homOfLE inf_le_left) R n)
    (-(SSet.homologyMap (SSet.Subcomplex.homOfLE inf_le_right) R n))

/-- `H_n(A) ⊞ H_n(B) ⟶ H_n(A ⊔ B)`, `(x, y) ↦ x + y` -/
def mvDesc (n : ℕ) :
    ((A : SSet.{u}).homology R n ⊞ (B : SSet.{u}).homology R n) ⟶
      ((A ⊔ B : K.Subcomplex) : SSet.{u}).homology R n :=
  biprod.desc (SSet.homologyMap (SSet.Subcomplex.homOfLE le_sup_left) R n)
    (SSet.homologyMap (SSet.Subcomplex.homOfLE le_sup_right) R n)

@[simp]
lemma mvLift_fst (n : ℕ) :
    mvLift A B R n ≫ biprod.fst =
      SSet.homologyMap (SSet.Subcomplex.homOfLE inf_le_left) R n :=
  biprod.lift_fst _ _

@[simp]
lemma mvLift_snd (n : ℕ) :
    mvLift A B R n ≫ biprod.snd =
      -SSet.homologyMap (SSet.Subcomplex.homOfLE inf_le_right) R n :=
  biprod.lift_snd _ _

@[simp]
lemma inl_mvDesc (n : ℕ) :
    biprod.inl ≫ mvDesc A B R n =
      SSet.homologyMap (SSet.Subcomplex.homOfLE le_sup_left) R n :=
  biprod.inl_desc _ _

@[simp]
lemma inr_mvDesc (n : ℕ) :
    biprod.inr ≫ mvDesc A B R n =
      SSet.homologyMap (SSet.Subcomplex.homOfLE le_sup_right) R n :=
  biprod.inr_desc _ _

lemma homologyMap_lift_homologyBiprodIso_hom (n : ℕ) :
    homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n ≫ (homologyBiprodIso A B R n).hom =
      mvLift A B R n := by
  dsimp only [homologyBiprodIso, mvLift]
  apply biprod.hom_ext
  · simp [← homologyMap_comp]
  · simp [← homologyMap_comp, homologyMap_neg]

lemma homologyBiprodIso_inv_homologyMap_desc (n : ℕ) :
    (homologyBiprodIso A B R n).inv ≫ homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) n =
      mvDesc A B R n := by
  dsimp only [homologyBiprodIso, mvDesc]
  apply biprod.hom_ext'
  · simp [← homologyMap_comp]
  · simp [← homologyMap_comp]

@[reassoc (attr := simp)]
lemma mvδ_mvLift (n : ℕ) : mvδ A B R n ≫ mvLift A B R n = 0 := by
  rw [← homologyMap_lift_homologyBiprodIso_hom, mvδ_comp_assoc, zero_comp]

@[reassoc (attr := simp)]
lemma mvLift_mvDesc (n : ℕ) : mvLift A B R n ≫ mvDesc A B R n = 0 := by
  rw [← homologyMap_lift_homologyBiprodIso_hom, ← homologyBiprodIso_inv_homologyMap_desc,
    Category.assoc, Iso.hom_inv_id_assoc, homologyMap_lift_desc]

@[reassoc (attr := simp)]
lemma mvDesc_mvδ (n : ℕ) : mvDesc A B R (n + 1) ≫ mvδ A B R n = 0 := by
  rw [← homologyBiprodIso_inv_homologyMap_desc, Category.assoc, comp_mvδ, comp_zero]

/-- `H_{n+1}(A ⊔ B) ⟶ H_n(A ⊓ B) ⟶ H_n(A) ⊞ H_n(B)` is exact -/
theorem mv_exact₁' (n : ℕ) :
    (ShortComplex.mk (mvδ A B R n) (mvLift A B R n) (mvδ_mvLift A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₁ A B R n)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (homologyBiprodIso A B R n)
    (by simp) (by simp [homologyMap_lift_homologyBiprodIso_hom])

/-- `H_n(A ⊓ B) ⟶ H_n(A) ⊞ H_n(B) ⟶ H_n(A ⊔ B)` is exact -/
theorem mv_exact₂' (n : ℕ) :
    (ShortComplex.mk (mvLift A B R n) (mvDesc A B R n) (mvLift_mvDesc A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₂ A B R n)
  exact ShortComplex.isoMk (Iso.refl _) (homologyBiprodIso A B R n) (Iso.refl _)
    (by simp [homologyMap_lift_homologyBiprodIso_hom])
    (by simp [← homologyBiprodIso_inv_homologyMap_desc])

/-- `H_{n+1}(A) ⊞ H_{n+1}(B) ⟶ H_{n+1}(A ⊔ B) ⟶ H_n(A ⊓ B)` is exact -/
theorem mv_exact₃' (n : ℕ) :
    (ShortComplex.mk (mvDesc A B R (n + 1)) (mvδ A B R n) (mvDesc_mvδ A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₃ A B R n)
  exact ShortComplex.isoMk (homologyBiprodIso A B R (n + 1)) (Iso.refl _) (Iso.refl _)
    (by simp [← homologyBiprodIso_inv_homologyMap_desc]) (by simp)

/-! ### Excision at the chain level: `C(B)/C(A ⊓ B) ≅ C(A ⊔ B)/C(A)` -/

/-- the pair `A ↪ A ⊔ B` -/
abbrev pairSup : SSetPair.{u} :=
  SSetPair.of (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))

/-- the pair `A ⊓ B ↪ B` -/
abbrev pairInf : SSetPair.{u} :=
  SSetPair.of (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))

/-- `C(B)/C(A ⊓ B) ≅ C(A ⊔ B)/C(A)`, induced by the inclusion `B ↪ A ⊔ B` -/
def cokerIso : (pairInf A B).chainComplex R ≅ (pairSup A B).chainComplex R :=
  pushoutCokernelIso (isPushout A B R) ((pairInf A B).isColimitCokernelCoforkChainComplex R)
    ((pairSup A B).isColimitCokernelCoforkChainComplex R)

@[reassoc (attr := simp)]
lemma chainComplexπ_cokerIso_hom :
    (pairInf A B).chainComplexπ R ≫ (cokerIso A B R).hom =
      j₂ A B R ≫ (pairSup A B).chainComplexπ R :=
  π_pushoutCokernelIso_hom (isPushout A B R) _ _

/-- `H_n(B, A ⊓ B) ≅ H_n(A ⊔ B, A)` -/
def homologyCokerIso (n : ℕ) : (pairInf A B).homology R n ≅ (pairSup A B).homology R n :=
  homologyMapIso (cokerIso A B R) n

/-- naturality of `chainComplexπ` in the pair -/
@[reassoc]
lemma chainComplexMap_right_chainComplexπ {P P' : SSetPair.{u}} (φ : P ⟶ P') :
    SSet.chainComplexMap φ.right R ≫ P'.chainComplexπ R =
      P.chainComplexπ R ≫ SSetPair.chainComplexMap φ R :=
  ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R).naturality φ

/-- naturality of `homologyπ` in the pair -/
@[reassoc]
lemma homologyMap_right_homologyπ {P P' : SSetPair.{u}} (φ : P ⟶ P') (n : ℕ) :
    SSet.homologyMap φ.right R n ≫ P'.homologyπ R n =
      P.homologyπ R n ≫ SSetPair.homologyMap φ R n := by
  simp only [SSetPair.homologyπ, SSetPair.homologyMap, SSet.homologyMap, ← homologyMap_comp,
    chainComplexMap_right_chainComplexπ]

/-- the morphism of pairs `(B, A ⊓ B) ⟶ (A ⊔ B, A)` -/
def excisionPairMap : pairInf A B ⟶ pairSup A B :=
  SSetPair.homMk (SSet.Subcomplex.homOfLE inf_le_left) (SSet.Subcomplex.homOfLE le_sup_right)
    rfl

lemma excisionPairMap_right :
    (excisionPairMap A B).right = SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B) := rfl

lemma excisionPairMap_left :
    (excisionPairMap A B).left = SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A) := rfl

lemma chainComplexMap_excisionPairMap :
    SSetPair.chainComplexMap (excisionPairMap A B) R = (cokerIso A B R).hom := by
  apply Cofork.IsColimit.hom_ext ((pairInf A B).isColimitCokernelCoforkChainComplex R)
  dsimp only [SSetPair.cokernelCoforkChainComplex]
  rw [Cofork.π_ofπ, ← chainComplexMap_right_chainComplexπ, chainComplexπ_cokerIso_hom]
  rfl

instance isIso_chainComplexMap_excisionPairMap :
    IsIso (SSetPair.chainComplexMap (excisionPairMap A B) R) := by
  rw [chainComplexMap_excisionPairMap]
  infer_instance

lemma homologyMap_excisionPairMap (n : ℕ) :
    SSetPair.homologyMap (excisionPairMap A B) R n = (homologyCokerIso A B R n).hom := by
  simp only [SSetPair.homologyMap, chainComplexMap_excisionPairMap, homologyCokerIso,
    homologyMapIso_hom]

/-- excision at the level of subcomplexes: the morphism of pairs `(B, A ⊓ B) ⟶ (A ⊔ B, A)`
induces an isomorphism `H_n(B, A ⊓ B) ≅ H_n(A ⊔ B, A)` -/
instance isIso_homologyMap_excisionPairMap (n : ℕ) :
    IsIso (SSetPair.homologyMap (excisionPairMap A B) R n) := by
  rw [homologyMap_excisionPairMap]
  infer_instance

@[reassoc]
lemma homologyπ_homologyCokerIso_hom (n : ℕ) :
    (pairInf A B).homologyπ R n ≫ (homologyCokerIso A B R n).hom =
      SSet.homologyMap (excisionPairMap A B).right R n ≫ (pairSup A B).homologyπ R n := by
  rw [← homologyMap_excisionPairMap, homologyMap_right_homologyπ]

end PoincareHighDim.SingularPair
