import Submission.Homology.Subdivision

/-!
# The diameter bound for barycentric subdivision and small simplices

Simplices of the `j`-th barycentric subdivision of an affine `m`-simplex have (weight-)diameter
at most `(m/(m+1))^j` times the diameter of the simplex, and all simplices produced by `Sd` and
`T` lie in the convex hull of the original simplex.  Together with the Lebesgue number lemma on
the compact standard simplex this gives: for an open cover (by interiors) `U` of `X`, every
singular simplex `σ` is `k`-small (`IsSmall U σ k`) for some `k`, and then all simplices of
`S^j σ` and `T S^j σ` (`j ≥ k`) have image in some `U i`.
-/

open CategoryTheory Limits AlgebraicTopology Convexity

noncomputable section

universe u

namespace PoincareHighDim.SingularPair

/-! ### Supports -/

namespace AffChain

lemma mem_support_of_linearMap {α β : Type*} (f : (α →₀ ℤ) →ₗ[ℤ] (β →₀ ℤ))
    (c : α →₀ ℤ) {y : β} (hy : y ∈ (f c).support) :
    ∃ x ∈ c.support, y ∈ (f (Finsupp.single x 1)).support := by
  classical
  have : f c = c.sum fun x z => z • f (Finsupp.single x 1) := by
    conv_lhs => rw [← Finsupp.sum_single c]
    rw [map_finsuppSum]
    refine Finsupp.sum_congr fun x _ => ?_
    rw [← map_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [this] at hy
  obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hy)
  exact ⟨x, hx, Finsupp.support_smul hy⟩

lemma eq_of_mem_support_single {α : Type*} {x y : α} (z : ℤ)
    (hy : y ∈ (Finsupp.single x z).support) : y = x := by
  classical
  have := Finsupp.support_single_subset hy
  simpa using this

lemma mem_support_coneL {n k : ℕ} (b : Δ n) (c : AffChain k n) {w' : Fin (k + 2) → Δ n}
    (hw' : w' ∈ (coneL b k c).support) : ∃ w ∈ c.support, w' = cone b w := by
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hw')
  exact ⟨w, hw, rfl⟩

lemma mem_support_bd_single {n k : ℕ} (w : Fin (k + 2) → Δ n) {w' : Fin (k + 1) → Δ n}
    (hw' : w' ∈ (bd k (Finsupp.single w 1)).support) :
    ∃ i : Fin (k + 2), w' = w ∘ i.succAbove := by
  classical
  rw [bd_single] at hw'
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hw')
  exact ⟨i, eq_of_mem_support_single _ (Finsupp.support_smul hi)⟩

/-! ### Convex hulls -/

/-- the convex hull (in weight coordinates) of the vertices `v` -/
abbrev hull {m n : ℕ} (v : Fin (m + 1) → Δ n) : Set (Fin (n + 1) → ℝ) :=
  _root_.convexHull ℝ (Set.range (wt ∘ v))

lemma range_subset_hull {m n : ℕ} (v : Fin (m + 1) → Δ n) : Set.range (wt ∘ v) ⊆ hull v :=
  subset_convexHull ℝ _

lemma hull_mono_of_subset {m m' n : ℕ} {v : Fin (m + 1) → Δ n} {v' : Fin (m' + 1) → Δ n}
    (h : Set.range (wt ∘ v') ⊆ hull v) : hull v' ⊆ hull v :=
  convexHull_min h (convex_convexHull ℝ _)

lemma range_comp_succAbove_subset_hull {m n : ℕ} (v : Fin (m + 2) → Δ n) (i : Fin (m + 2)) :
    Set.range (wt ∘ (v ∘ i.succAbove)) ⊆ hull v := by
  rintro _ ⟨j, rfl⟩
  exact subset_convexHull ℝ _ ⟨i.succAbove j, rfl⟩

lemma wt_bary_mem_hull {m n : ℕ} (v : Fin (m + 1) → Δ n) : wt (bary v) ∈ hull v := by
  rw [wt_bary]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => by positivity)
    (by simp [Finset.sum_const, Finset.card_univ]; field_simp)
    (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)

lemma range_cone_subset {m n : ℕ} (b : Δ n) (v : Fin m → Δ n) {S : Set (Fin (n + 1) → ℝ)}
    (hb : wt b ∈ S) (hv : Set.range (wt ∘ v) ⊆ S) : Set.range (wt ∘ cone b v) ⊆ S := by
  rintro _ ⟨j, rfl⟩
  refine Fin.cases hb (fun j => hv ⟨j, rfl⟩) j

/-- all simplices of `Sd [w]` lie in the convex hull of `w` -/
theorem range_subset_hull_of_mem_support_Sd {n : ℕ} : ∀ (k : ℕ) (w : Fin (k + 1) → Δ n)
    (w' : Fin (k + 1) → Δ n), w' ∈ (Sd k (Finsupp.single w 1)).support →
    Set.range (wt ∘ w') ⊆ hull w
  | 0, w, w', hw' => by
    rw [Sd_zero, LinearMap.id_apply] at hw'
    rw [eq_of_mem_support_single _ hw']
    exact range_subset_hull w
  | k + 1, w, w', hw' => by
    rw [Sd_succ_single, one_smul] at hw'
    obtain ⟨w'', hw'', rfl⟩ := mem_support_coneL _ _ hw'
    obtain ⟨w₁, hw₁, hw''⟩ := mem_support_of_linearMap (Sd k) _ hw''
    obtain ⟨i, rfl⟩ := mem_support_bd_single w hw₁
    exact range_cone_subset _ _ (wt_bary_mem_hull w)
      ((range_subset_hull_of_mem_support_Sd k _ _ hw'').trans
        (hull_mono_of_subset (range_comp_succAbove_subset_hull w i)))

/-- all simplices of `T [w]` lie in the convex hull of `w` -/
theorem range_subset_hull_of_mem_support_T {n : ℕ} : ∀ (k : ℕ) (w : Fin (k + 1) → Δ n)
    (w' : Fin (k + 2) → Δ n), w' ∈ (T k (Finsupp.single w 1)).support →
    Set.range (wt ∘ w') ⊆ hull w
  | 0, w, w', hw' => by
    rw [T_zero_single, one_smul] at hw'
    obtain ⟨w'', hw'', rfl⟩ := mem_support_coneL _ _ hw'
    rw [eq_of_mem_support_single _ hw'']
    exact range_cone_subset _ _ (wt_bary_mem_hull w) (range_subset_hull w)
  | k + 1, w, w', hw' => by
    classical
    rw [T_succ_single, one_smul] at hw'
    obtain ⟨w'', hw'', rfl⟩ := mem_support_coneL _ _ hw'
    refine range_cone_subset _ _ (wt_bary_mem_hull w) ?_
    rcases Finset.mem_union.mp (Finsupp.support_sub hw'') with h | h
    · rw [eq_of_mem_support_single _ h]
      exact range_subset_hull w
    · obtain ⟨w₁, hw₁, h⟩ := mem_support_of_linearMap (T k) _ h
      obtain ⟨i, rfl⟩ := mem_support_bd_single w hw₁
      exact (range_subset_hull_of_mem_support_T k _ _ h).trans
        (hull_mono_of_subset (range_comp_succAbove_subset_hull w i))

theorem range_subset_hull_of_mem_support_SdPow {n : ℕ} (k : ℕ) (w : Fin (k + 1) → Δ n) :
    ∀ (j : ℕ) (w' : Fin (k + 1) → Δ n), w' ∈ (SdPow k j (Finsupp.single w 1)).support →
    Set.range (wt ∘ w') ⊆ hull w
  | 0, w', hw' => by
    rw [SdPow_zero, LinearMap.id_apply] at hw'
    rw [eq_of_mem_support_single _ hw']
    exact range_subset_hull w
  | j + 1, w', hw' => by
    rw [SdPow_succ, LinearMap.comp_apply] at hw'
    obtain ⟨w₁, hw₁, hw'⟩ := mem_support_of_linearMap (Sd k) _ hw'
    exact (range_subset_hull_of_mem_support_Sd k _ _ hw').trans
      (hull_mono_of_subset (range_subset_hull_of_mem_support_SdPow k w j _ hw₁))

/-! ### The diameter bound -/

lemma diam_range_le_of_range_subset_hull {m m' n : ℕ} {v : Fin (m + 1) → Δ n}
    {v' : Fin (m' + 1) → Δ n} (h : Set.range (wt ∘ v') ⊆ hull v) :
    Metric.diam (Set.range (wt ∘ v')) ≤ Metric.diam (Set.range (wt ∘ v)) := by
  rw [← convexHull_diam (Set.range (wt ∘ v))]
  exact Metric.diam_mono h (isBounded_convexHull.mpr (isBounded_range_wt_comp v))

lemma diam_range_fin_one {n : ℕ} (v : Fin 1 → Δ n) :
    Metric.diam (Set.range (wt ∘ v)) = 0 := by
  refine Metric.diam_subsingleton ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  obtain rfl : i = j := Fin.ext (by omega)
  rfl

lemma div_succ_le_div_succ {a b : ℕ} (h : a ≤ b) : (a / (a + 1) : ℝ) ≤ b / (b + 1) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  nlinarith

lemma div_succ_nonneg (a : ℕ) : (0 : ℝ) ≤ a / (a + 1) := by positivity

lemma div_succ_lt_one (a : ℕ) : (a / (a + 1) : ℝ) < 1 := by
  rw [div_lt_one (by positivity)]
  linarith

/-- distance from the barycenter to a point of the hull -/
lemma dist_wt_bary_le_of_mem_hull {m n : ℕ} (v : Fin (m + 1) → Δ n) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ hull v) :
    dist (wt (bary v)) x ≤ (m / (m + 1 : ℝ)) * Metric.diam (Set.range (wt ∘ v)) := by
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := convexHull_exists_dist_ge hx (wt (bary v))
  rw [dist_comm]
  exact hj.trans (by rw [dist_comm]; exact dist_wt_bary_le v j)

/-- the diameter bound for one subdivision -/
theorem diam_le_of_mem_support_Sd {n : ℕ} : ∀ (k : ℕ) (w : Fin (k + 1) → Δ n)
    (w' : Fin (k + 1) → Δ n), w' ∈ (Sd k (Finsupp.single w 1)).support →
    Metric.diam (Set.range (wt ∘ w')) ≤ (k / (k + 1 : ℝ)) * Metric.diam (Set.range (wt ∘ w))
  | 0, w, w', _ => by
    rw [diam_range_fin_one]
    positivity
  | k + 1, w, w', hw' => by
    have hb := isBounded_range_wt_comp w
    have hw₀ := hw'
    rw [Sd_succ_single, one_smul] at hw₀
    obtain ⟨w'', hw₂, rfl⟩ := mem_support_coneL _ _ hw₀
    obtain ⟨w₁, hw₁, hw₃⟩ := mem_support_of_linearMap (Sd k) _ hw₂
    obtain ⟨i, rfl⟩ := mem_support_bd_single w hw₁
    have hsub : Set.range (wt ∘ w'') ⊆ hull w :=
      (range_subset_hull_of_mem_support_Sd k _ _ hw₃).trans
        (hull_mono_of_subset (range_comp_succAbove_subset_hull w i))
    -- the inductive bound on `w''`
    have h1 : Metric.diam (Set.range (wt ∘ w'')) ≤
        ((k + 1 : ℕ) / ((k + 1 : ℕ) + 1 : ℝ)) * Metric.diam (Set.range (wt ∘ w)) := by
      refine (diam_le_of_mem_support_Sd k _ _ hw₃).trans ?_
      refine mul_le_mul (div_succ_le_div_succ (Nat.le_succ k)) ?_ Metric.diam_nonneg
        (div_succ_nonneg _)
      exact diam_range_le_of_range_subset_hull (range_comp_succAbove_subset_hull w i)
    -- the bound on distances to the barycenter
    have h2 : ∀ x ∈ Set.range (wt ∘ w''), dist (wt (bary w)) x ≤
        ((k + 1 : ℕ) / ((k + 1 : ℕ) + 1 : ℝ)) * Metric.diam (Set.range (wt ∘ w)) :=
      fun x hx => dist_wt_bary_le_of_mem_hull w (hsub hx)
    have hC : 0 ≤
        ((k + 1 : ℕ) / ((k + 1 : ℕ) + 1 : ℝ)) * Metric.diam (Set.range (wt ∘ w)) :=
      mul_nonneg (div_succ_nonneg _) Metric.diam_nonneg
    refine Metric.diam_le_of_forall_dist_le hC ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · simp only [Function.comp_apply, cone, Fin.cons_zero, dist_self]; exact hC
    · simpa [cone] using h2 _ ⟨b, rfl⟩
    · rw [dist_comm]; simpa [cone] using h2 _ ⟨a, rfl⟩
    · simp only [Function.comp_apply, cone, Fin.cons_succ]
      exact (Metric.dist_le_diam_of_mem (isBounded_range_wt_comp w'') ⟨a, rfl⟩
        ⟨b, rfl⟩).trans h1

/-- the diameter bound for iterated subdivision -/
theorem diam_le_of_mem_support_SdPow {n : ℕ} (k : ℕ) (w : Fin (k + 1) → Δ n) :
    ∀ (j : ℕ) (w' : Fin (k + 1) → Δ n), w' ∈ (SdPow k j (Finsupp.single w 1)).support →
    Metric.diam (Set.range (wt ∘ w')) ≤
      (k / (k + 1 : ℝ)) ^ j * Metric.diam (Set.range (wt ∘ w))
  | 0, w', hw' => by
    rw [SdPow_zero, LinearMap.id_apply] at hw'
    rw [eq_of_mem_support_single _ hw', pow_zero, one_mul]
  | j + 1, w', hw' => by
    rw [SdPow_succ, LinearMap.comp_apply] at hw'
    obtain ⟨w₁, hw₁, hw'⟩ := mem_support_of_linearMap (Sd k) _ hw'
    refine (diam_le_of_mem_support_Sd k _ _ hw').trans ?_
    rw [pow_succ', mul_assoc]
    exact mul_le_mul_of_nonneg_left (diam_le_of_mem_support_SdPow k w j _ hw₁) (div_succ_nonneg _)

lemma diam_range_wt_comp_le_one {m n : ℕ} (v : Fin (m + 1) → Δ n) :
    Metric.diam (Set.range (wt ∘ v)) ≤ 1 :=
  (Metric.diam_mono (by rintro _ ⟨i, rfl⟩; exact ⟨v i, rfl⟩) (isBounded_range_wt n)).trans
    (diam_range_wt_le n)

/-- simplices of the `j`-th subdivision of the identity simplex have diameter `≤ (k/(k+1))^j` -/
theorem diam_le_of_mem_support_SdPow_idVerts (k j : ℕ) (w' : Fin (k + 1) → Δ k)
    (hw' : w' ∈ (SdPow k j (Finsupp.single (idVerts k) 1)).support) :
    Metric.diam (Set.range (wt ∘ w')) ≤ (k / (k + 1 : ℝ)) ^ j := by
  refine (diam_le_of_mem_support_SdPow k _ j w' hw').trans ?_
  calc (k / (k + 1 : ℝ)) ^ j * Metric.diam (Set.range (wt ∘ idVerts k))
      ≤ (k / (k + 1 : ℝ)) ^ j * 1 :=
        mul_le_mul_of_nonneg_left (diam_range_wt_comp_le_one _) (by positivity)
    _ = (k / (k + 1 : ℝ)) ^ j := mul_one _

end AffChain

/-! ### Small simplices -/

open AffChain

lemma continuous_wt (n : ℕ) : Continuous (wt (n := n)) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous

lemma isCompact_range_wt (n : ℕ) : IsCompact (Set.range (wt (n := n))) :=
  isCompact_range (continuous_wt n)

/-- the image of a subset `s` of `Δ m` under an affine simplex `w` lies in the hull of `w` -/
lemma image_affineSimplex_subset_hull {m n : ℕ} (w : Fin (m + 1) → Δ n) :
    wt '' Set.range (affineSimplex w) ⊆ hull w := by
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  exact wt_affineSimplex_mem_convexHull w t

lemma diam_image_range_affineSimplex_le {m n : ℕ} (w : Fin (m + 1) → Δ n) :
    Metric.diam (wt '' Set.range (affineSimplex w)) ≤ Metric.diam (Set.range (wt ∘ w)) := by
  rw [← convexHull_diam (Set.range (wt ∘ w))]
  exact Metric.diam_mono (image_affineSimplex_subset_hull w)
    (isBounded_convexHull.mpr (isBounded_range_wt_comp w))

variable {X : TopCat.{u}} {ι : Type*} (U : ι → Set X)

/-- `σ` is `k`-small for the cover `U`: every subset of `Δ m` of weight-diameter at most
`(m/(m+1))^k` is mapped by `σ` into some `U i` -/
def IsSmall {m : ℕ} (σ : C(Δ m, X)) (k : ℕ) : Prop :=
  ∀ s : Set (Δ m), Metric.diam (wt '' s) ≤ (m / (m + 1 : ℝ)) ^ k → ∃ i, σ '' s ⊆ U i

variable {U}

lemma IsSmall.mono {m : ℕ} {σ : C(Δ m, X)} {k k' : ℕ} (h : IsSmall U σ k) (hk : k ≤ k') :
    IsSmall U σ k' := fun s hs =>
  h s (hs.trans (pow_le_pow_of_le_one (div_succ_nonneg m) (div_succ_lt_one m).le hk))

/-- faces (and more generally injective index maps) of small simplices are small -/
lemma IsSmall.comp_map {m m' : ℕ} {σ : C(Δ m, X)} {k : ℕ} (h : IsSmall U σ k)
    (f : Fin (m' + 1) → Fin (m + 1)) (hf : Function.Injective f) (hm : m' ≤ m) :
    IsSmall U (σ.comp ⟨StdSimplex.map f, StdSimplex.continuous_map ℝ f⟩) k := by
  intro s hs
  have hb : Bornology.IsBounded (wt '' s) :=
    isBounded_of_subset_range_wt (by rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩)
  obtain ⟨i, hi⟩ := h (StdSimplex.map f '' s) (by
    refine (Metric.diam_le_of_forall_dist_le (by positivity) ?_).trans
      (hs.trans (pow_le_pow_left₀ (div_succ_nonneg m') (div_succ_le_div_succ hm) k))
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb', rfl⟩, rfl⟩
    exact (dist_wt_map_le f hf a b).trans
      (Metric.dist_le_diam_of_mem hb ⟨a, ha, rfl⟩ ⟨b, hb', rfl⟩))
  refine ⟨i, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hi ⟨StdSimplex.map f t, ⟨t, ht, rfl⟩, rfl⟩

/-- faces of small singular simplices are small -/
lemma IsSmall.δ {m : ℕ} {τ : Sing X (m + 1)} {k : ℕ} (h : IsSmall U (X.toSSetObjEquiv _ τ) k)
    (i : Fin (m + 2)) :
    IsSmall U (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i τ)) k :=
  h.comp_map i.succAbove Fin.succAbove_right_injective (Nat.le_succ m)

/-- the Lebesgue number argument: every singular simplex is small for some `k` -/
theorem exists_isSmall (hU : ⋃ i, interior (U i) = Set.univ) {m : ℕ} (σ : C(Δ m, X)) :
    ∃ k, IsSmall U σ k := by
  -- the open cover of `Δ m` by the preimages of the interiors, written through the embedding `wt`
  have hV : ∀ i, ∃ W : Set (Fin (m + 1) → ℝ),
      IsOpen W ∧ wt ⁻¹' W = σ ⁻¹' interior (U i) :=
    fun i => (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).isInducing.isOpen_iff.mp
      (isOpen_interior.preimage σ.continuous)
  choose W hWo hW using hV
  have hcov : Set.range (wt (n := m)) ⊆ ⋃ i, W i := by
    rintro _ ⟨t, rfl⟩
    have : σ t ∈ ⋃ i, interior (U i) := hU ▸ Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp this
    exact Set.mem_iUnion.mpr ⟨i, by rw [← Set.mem_preimage, hW]; exact hi⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_range_wt m) hWo hcov
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (div_succ_lt_one m)
  refine ⟨k, fun s hs => ?_⟩
  rcases s.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · -- the cover is nonempty since `Δ m` is
    have : (StdSimplex.single 0 : Δ m) ∈ ⋃ i, σ ⁻¹' interior (U i) := by
      have := hU ▸ Set.mem_univ (σ (StdSimplex.single 0))
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp this
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    obtain ⟨i, -⟩ := Set.mem_iUnion.mp this
    exact ⟨i, by simp⟩
  obtain ⟨i, hi⟩ := hball (wt t₀) ⟨t₀, rfl⟩
  refine ⟨i, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hb : Bornology.IsBounded (wt '' s) :=
    isBounded_of_subset_range_wt (by rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩)
  have : wt t ∈ Metric.ball (wt t₀) δ := by
    rw [Metric.mem_ball]
    exact (Metric.dist_le_diam_of_mem hb ⟨t, ht, rfl⟩ ⟨t₀, ht₀, rfl⟩).trans_lt
      (hs.trans_lt hk)
  have := hi this
  rw [← Set.mem_preimage, hW] at this
  exact interior_subset this

/-- for a `k`-small `σ`, every affine simplex `w` of `Δ m` of small diameter is sent into
some `U i` -/
lemma IsSmall.affSing_mem {m : ℕ} {σ : C(Δ m, X)} {k : ℕ} (h : IsSmall U σ k) {k' : ℕ}
    {w : Fin (k' + 1) → Δ m}
    (hw : Metric.diam (Set.range (wt ∘ w)) ≤ (m / (m + 1 : ℝ)) ^ k) :
    ∃ i, affSing σ w ∈ (singSub X (U i)).obj _ := by
  obtain ⟨i, hi⟩ :=
    h (Set.range (affineSimplex w)) ((diam_image_range_affineSimplex_le w).trans hw)
  refine ⟨i, (mem_singSub_iff X (U i) _).mpr ?_⟩
  rw [toSSetObjEquiv_affSing]
  rintro _ ⟨t, rfl⟩
  exact hi ⟨affineSimplex w t, ⟨t, rfl⟩, rfl⟩

/-- simplices of `S^j σ` are in the cover for `j ≥ k` -/
theorem IsSmall.SdPow_mem {m : ℕ} {σ : C(Δ m, X)} {k : ℕ} (h : IsSmall U σ k) {j : ℕ}
    (hj : k ≤ j) (w : Fin (m + 1) → Δ m)
    (hw : w ∈ (SdPow m j (Finsupp.single (idVerts m) 1)).support) :
    ∃ i, affSing σ w ∈ (singSub X (U i)).obj _ :=
  h.affSing_mem ((diam_le_of_mem_support_SdPow_idVerts m j w hw).trans
    (pow_le_pow_of_le_one (div_succ_nonneg m) (div_succ_lt_one m).le hj))

/-- simplices of `T S^j σ` are in the cover for `j ≥ k` -/
theorem IsSmall.T_SdPow_mem {m : ℕ} {σ : C(Δ m, X)} {k : ℕ} (h : IsSmall U σ k) {j : ℕ}
    (hj : k ≤ j) (w : Fin (m + 2) → Δ m)
    (hw : w ∈ (T m (SdPow m j (Finsupp.single (idVerts m) 1))).support) :
    ∃ i, affSing σ w ∈ (singSub X (U i)).obj _ := by
  obtain ⟨w₁, hw₁, hw⟩ := mem_support_of_linearMap (T m) _ hw
  refine h.affSing_mem ?_
  refine (diam_range_le_of_range_subset_hull (range_subset_hull_of_mem_support_T m w₁ w hw)).trans
    ((diam_le_of_mem_support_SdPow_idVerts m j w₁ hw₁).trans
      (pow_le_pow_of_le_one (div_succ_nonneg m) (div_succ_lt_one m).le hj))

variable (R : ModuleCat.{u} ℤ)

/-- for `j ≥ k` and a `k`-small `σ`, `S^j` of the generator `σ` comes from the chains of any
subcomplex `A` containing all `singSub X (U i)` -/
theorem IsSmall.ι_SPow_f_eq {m : ℕ} {σ : C(Δ m, X)} {k : ℕ} (h : IsSmall U σ k) {j : ℕ}
    (hj : k ≤ j) (A : (TopCat.toSSet.obj X).Subcomplex) (hA : ∀ i, singSub X (U i) ≤ A) :
    (TopCat.toSSet.obj X).ιChainComplex (sing σ) ≫ (SPow R X j).f m =
      toChainSub R A σ m (SdPow m j (Finsupp.single (idVerts m) 1)) ≫
        (SSet.chainComplexMap A.ι R).f m := by
  rw [ι_SPow_f, Equiv.apply_symm_apply, toChain_eq_toChainSub R A]
  intro w hw
  obtain ⟨i, hi⟩ := h.SdPow_mem hj w hw
  exact hA i _ hi

/-- for `j ≥ k` and a `k`-small `σ`, `T S^j` of the generator `σ` comes from the chains of any
subcomplex `A` containing all `singSub X (U i)` -/
theorem IsSmall.ι_SPow_f_TMap_eq {m : ℕ} {σ : C(Δ m, X)} {k : ℕ} (h : IsSmall U σ k)
    {j : ℕ} (hj : k ≤ j) (A : (TopCat.toSSet.obj X).Subcomplex)
    (hA : ∀ i, singSub X (U i) ≤ A) :
    (TopCat.toSSet.obj X).ιChainComplex (sing σ) ≫ (SPow R X j).f m ≫ TMap R X m =
      toChainSub R A σ (m + 1) (T m (SdPow m j (Finsupp.single (idVerts m) 1))) ≫
        (SSet.chainComplexMap A.ι R).f (m + 1) := by
  rw [ι_SPow_f_assoc, Equiv.apply_symm_apply, toChain_TMap, toChain_eq_toChainSub R A]
  intro w hw
  obtain ⟨i, hi⟩ := h.T_SdPow_mem hj w hw
  exact hA i _ hi

end PoincareHighDim.SingularPair
