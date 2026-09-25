import Submission.Homology.SingularPair

/-!
# The Bockstein short exact sequence of coefficients

For `d : ℕ` we consider the short exact sequence of coefficient objects
`0 → ℤ →(·d) ℤ → ℤ/d → 0` in `ModuleCat.{u} ℤ` (with `ℤ` and `ℤ/d` lifted to universe `u`:
`Z = ModuleCat.of ℤ (ULift ℤ)`, `Zd d = ModuleCat.of ℤ (ULift (ZMod d))`).  Applying the
singular chain complex functor of a space `X` degreewise gives the short exact sequence of
chain complexes `0 → C(X;ℤ) →d C(X;ℤ) → C(X;ℤ/d) → 0` (`bocksteinSC`,
`bocksteinSC_shortExact`): degreewise the maps are coproducts of copies of the coefficient
maps, and coproducts are exact in `ModuleCat ℤ` (AB4, which we derive from AB5 through the
forgetful functor to abelian groups because Mathlib's instance only covers `ModuleCat.{u} R`
with `R : Type u`).

The associated homology long exact sequence (`bockstein_exact₁/₂/₃`) has as its first map
multiplication by `d` on `H_k(X;ℤ)` (`homologyMap_bockstein_f`); consequently if
`H_k(X;ℤ/d) = 0` then every class of `H_k(X;ℤ)` is divisible by `d`
(`exists_smul_eq_of_isZero`).
-/

open CategoryTheory Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

/-! ### Exactness of coproducts in `ModuleCat.{u} ℤ` -/

/-- `ModuleCat.{u} ℤ` satisfies AB5 (Mathlib's instance requires the ring to live in `Type u`). -/
instance ab5_moduleCat_int : AB5 (ModuleCat.{u} ℤ) :=
  ⟨fun J _ _ => HasExactColimitsOfShape.domain_of_functor J (forget₂ _ AddCommGrpCat.{u})⟩

attribute [local instance] Abelian.hasFiniteBiproducts in
instance ab4_moduleCat_int : AB4 (ModuleCat.{u} ℤ) := AB4.of_AB5 _

/-- the functor `R ↦ ∐ (fun _ : ι ↦ R)` -/
abbrev sigmaFun (ι : Type u) : ModuleCat.{u} ℤ ⥤ ModuleCat.{u} ℤ := sigmaConst.flip.obj ι

lemma sigmaFun_map (ι : Type u) {R R' : ModuleCat.{u} ℤ} (φ : R ⟶ R') :
    (sigmaFun ι).map φ = Limits.Sigma.map (fun _ : ι => φ) := rfl

/-- `sigmaFun ι` is the composite of the constant functor and `colim` -/
def sigmaFunIso (ι : Type u) :
    (Functor.const (Discrete ι) ⋙ colim : ModuleCat.{u} ℤ ⥤ _) ≅ sigmaFun ι :=
  NatIso.ofComponents (fun _ => HasColimit.isoOfNatIso Discrete.natIsoFunctor) (by
    intro R R' φ
    apply colimit.hom_ext
    rintro ⟨j⟩
    simp)

instance (ι : Type u) : (sigmaFun ι).Additive where
  map_add {_ _ f g} := by
    apply Sigma.hom_ext
    intro i
    simp [Preadditive.comp_add]

instance (ι : Type u) : PreservesFiniteLimits (sigmaFun ι) :=
  preservesFiniteLimits_of_natIso (sigmaFunIso ι)

instance (ι : Type u) : PreservesFiniteColimits (sigmaFun ι) :=
  preservesFiniteColimits_of_natIso (sigmaFunIso ι)

/-! ### The coefficient sequence `0 → ℤ → ℤ → ℤ/d → 0` -/

/-- coefficient object `ℤ/d` -/
abbrev Zd (d : ℕ) : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} (ZMod d))

instance (d : ℕ) [NeZero d] : Finite (Zd.{u} d) := inferInstanceAs (Finite (ULift (ZMod d)))

/-- multiplication by `d` -/
def mulD (d : ℕ) : Z.{u} ⟶ Z.{u} := ModuleCat.ofHom ((d : ℤ) • LinearMap.id)

/-- reduction mod `d` -/
def redD (d : ℕ) : Z.{u} ⟶ Zd.{u} d :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ
    (Int.castAddHom (ZMod d)).toIntLinearMap ∘ₗ ULift.moduleEquiv.toLinearMap)

lemma mulD_eq (d : ℕ) : mulD.{u} d = (d : ℤ) • 𝟙 Z.{u} := by
  ext x
  simp [mulD]

lemma mulD_hom_apply (d : ℕ) (x : Z.{u}) : (mulD d).hom x = ULift.up ((d : ℤ) * x.down) := rfl

lemma redD_hom_apply (d : ℕ) (x : Z.{u}) : (redD d).hom x = ULift.up (x.down : ZMod d) := rfl

lemma mulD_comp_redD (d : ℕ) : mulD.{u} d ≫ redD d = 0 := by
  ext x
  simp [mulD, redD]

/-- the short complex `ℤ →d ℤ → ℤ/d` -/
def coefSC (d : ℕ) : ShortComplex (ModuleCat.{u} ℤ) :=
  ShortComplex.mk (mulD d) (redD d) (mulD_comp_redD d)

theorem coefSC_shortExact (d : ℕ) [NeZero d] : (coefSC.{u} d).ShortExact := by
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne d
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have : (d : ℤ) ∣ x.down := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact congrArg ULift.down hx
    obtain ⟨c, hc⟩ := this
    exact ⟨ULift.up c, ULift.ext _ _ (by change (d : ℤ) * c = x.down; rw [hc])⟩
  · rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    have h : (d : ℤ) * x.down = (d : ℤ) * y.down := congrArg ULift.down hxy
    exact ULift.ext _ _ (mul_left_cancel₀ hd h)
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    exact ⟨ULift.up (y.down.cast : ℤ), ULift.ext _ _ (ZMod.intCast_zmod_cast y.down)⟩

/-! ### The Bockstein short exact sequence of singular chains -/

variable (d : ℕ) (X : TopCat.{u})

/-- the singular chain complex of `X` as a functor of the coefficients -/
abbrev chainsOf : ModuleCat.{u} ℤ ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{u} ℤ)).flip.obj X

lemma chainsOf_map_f {R R' : ModuleCat.{u} ℤ} (φ : R ⟶ R') (k : ℕ) :
    ((chainsOf X).map φ).f k =
      Limits.Sigma.map (fun _ : (TopCat.toSSet.obj X) _⦋k⦌ => φ) := rfl

/-- the short complex `C(X;ℤ) →d C(X;ℤ) → C(X;ℤ/d)` -/
def bocksteinSC : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map (mulD d)).app X)
    (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map (redD d)).app X)
    (by rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, mulD_comp_redD]; simp)

@[simp] lemma bocksteinSC_X₁ : (bocksteinSC d X).X₁ = C Z X := rfl
@[simp] lemma bocksteinSC_X₂ : (bocksteinSC d X).X₂ = C Z X := rfl
@[simp] lemma bocksteinSC_X₃ : (bocksteinSC d X).X₃ = C (Zd d) X := rfl

@[simp] lemma bocksteinSC_f :
    (bocksteinSC d X).f = ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map (mulD d)).app X :=
  rfl

@[simp] lemma bocksteinSC_g :
    (bocksteinSC d X).g = ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map (redD d)).app X :=
  rfl

lemma bocksteinSC_eq : bocksteinSC d X = (coefSC d).map (chainsOf X) := rfl

lemma bocksteinSC_map_eval (k : ℕ) :
    (bocksteinSC d X).map (eval _ _ k) =
      (coefSC d).map (sigmaFun ((TopCat.toSSet.obj X) _⦋k⦌)) := rfl

theorem bocksteinSC_shortExact [NeZero d] : (bocksteinSC d X).ShortExact := by
  rw [shortExact_iff_degreewise_shortExact]
  intro k
  rw [bocksteinSC_map_eval]
  exact (coefSC_shortExact d).map_of_exact _

/-! ### The Bockstein long exact sequence -/

/-- the Bockstein connecting morphism `H_{k+1}(X;ℤ/d) ⟶ H_k(X;ℤ)` -/
def bocksteinδ [NeZero d] (k : ℕ) : H (Zd d) X (k + 1) ⟶ H Z X k :=
  (bocksteinSC_shortExact d X).δ (k + 1) k rfl

theorem bockstein_exact₁ [NeZero d] (k : ℕ) :
    (ShortComplex.mk (bocksteinδ d X k) (homologyMap (bocksteinSC d X).f k)
      ((bocksteinSC_shortExact d X).δ_comp (k + 1) k rfl)).Exact :=
  (bocksteinSC_shortExact d X).homology_exact₁ (k + 1) k rfl

theorem bockstein_exact₂ [NeZero d] (k : ℕ) :
    (ShortComplex.mk (homologyMap (bocksteinSC d X).f k) (homologyMap (bocksteinSC d X).g k)
      (by rw [← homologyMap_comp, (bocksteinSC d X).zero, homologyMap_zero])).Exact :=
  (bocksteinSC_shortExact d X).homology_exact₂ k

theorem bockstein_exact₃ [NeZero d] (k : ℕ) :
    (ShortComplex.mk (homologyMap (bocksteinSC d X).g (k + 1)) (bocksteinδ d X k)
      ((bocksteinSC_shortExact d X).comp_δ (k + 1) k rfl)).Exact :=
  (bocksteinSC_shortExact d X).homology_exact₃ (k + 1) k rfl

/-- the first map of the Bockstein sequence is multiplication by `d` -/
theorem homologyMap_bockstein_f (k : ℕ) :
    homologyMap (bocksteinSC d X).f k = (d : ℤ) • 𝟙 (H Z X k) := by
  show homologyMap (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map (mulD d)).app X) k = _
  rw [mulD_eq, CategoryTheory.Functor.map_zsmul, NatTrans.app_zsmul,
    CategoryTheory.Functor.map_id, NatTrans.id_app]
  exact ((homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).map_zsmul).trans
    (by rw [CategoryTheory.Functor.map_id]; rfl)

/-- if `H_k(X;ℤ/d) = 0`, every integral class is divisible by `d` -/
theorem exists_smul_eq_of_isZero [NeZero d] (k : ℕ) (h : IsZero (H (Zd d) X k)) (g : H Z X k) :
    ∃ g' : H Z X k, (d : ℤ) • g' = g := by
  have hepi : Epi (homologyMap (bocksteinSC d X).f k) :=
    (bockstein_exact₂ d X k).epi_f (h.eq_zero_of_tgt _)
  obtain ⟨g', hg'⟩ := (ModuleCat.epi_iff_surjective _).1 hepi g
  refine ⟨g', ?_⟩
  rw [homologyMap_bockstein_f] at hg'
  rw [← hg']
  rfl

end PoincareHighDim.SingularPair
