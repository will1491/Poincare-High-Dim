import Submission.Morse.CancelGood

/-!
# Cancellation, step C4c (P): the off-`K` phase, the ball of `p`, and the middle band

For `k : c.CancelConsts` this module provides

* **the interior of the modification region** `K`: `p, q ∈ interior K`, and the modified field
  agrees with the original one off the interior (`V'_eq_V_of_notMem_interior`);
* **the off-`K` phase** (`exists_hit_K_or_bottom`): a trajectory starting in the strip either
  reaches the level `a'` or enters `K`, and before that it is off `K` and above `a'` (LaSalle
  with `-f` on the compact set `f⁻¹[a', b'] ∩ (interior K)ᶜ`, on which `f` strictly decreases);
* **the ball of `p`** (`exists_reach_Wp2_Tmid`): every trajectory starting in the ball region
  `Wball` reaches a point of `Wp2 ∩ Tmid` at the level `lo₂`;
* **the middle band**: the transverse coordinate is non-increasing on band segments
  (`antitoneOn_normSq_ζ_Φ_of_band`), band segments starting in `Sσ` lie in `Tmid`
  (`Φ_mem_Tmid_of_band`), the arc (`ζ = 0`) reaches the level `hi₁`
  (`exists_reach_hi₁_of_ζ_eq_zero`), and a band point with `‖ζ‖ ≥ 2δ` above `lo₂` moves
  strictly down (`exists_pos_mem_Tmid_of_two_δ_le`).

Conventions: fields descend (`df(V) ∈ [-1, 0]`), `morseNorm` is the Euclidean norm while
`Metric.ball` on `Fin n → ℝ` is the sup-norm ball; all dynamical lemmas carry explicit `hstay`
or region hypotheses.
-/

open Set Filter

namespace PoincareHighDim

open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split recombine_decompose)
open CancelModel

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}

variable {f : M → ℝ}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace CancelData

variable [DecidableEq M] {a' b' : ℝ} {p q : M} {c : CancelData I f a' b' p q}

namespace CancelConsts

variable (k : c.CancelConsts)

/-! ### The interior of `K` -/

/-- The open core of the pusher support `Kp`. -/
def KpInt : Set (Fin n → ℝ) :=
  {y | morseNorm n y < c.ρB ∧ perpSq c.e₁ y < k.τ ^ 2 * axial c.e₁ y ^ 2 + 2 * k.δ ^ 2 ∧
    -k.δ < axial c.e₁ y}

theorem isOpen_KpInt : IsOpen k.KpInt :=
  (isOpen_lt continuous_morseNorm continuous_const).inter
    ((isOpen_lt (continuous_perpSq _)
      ((continuous_const.mul ((continuous_axial _).pow 2)).add continuous_const)).inter
      (isOpen_lt continuous_const (continuous_axial _)))

theorem KpInt_subset_Kp : k.KpInt ⊆ Kp k.δ k.τ c.e₁ c.ρB := fun _ hy =>
  ⟨hy.1.le, hy.2.1.le, hy.2.2.le⟩

theorem isOpen_image_KpInt : IsOpen (c.e.χ '' k.KpInt) := by
  refine (c.e.χ.isOpen_image_iff_of_subset_source fun y hy => ?_).2 k.isOpen_KpInt
  exact c.e.hball (mem_ball_of_morseNorm_lt (hy.1.trans c.ρB_lt_R'))

theorem image_KpInt_subset_interior : c.e.χ '' k.KpInt ⊆ interior k.K :=
  k.isOpen_image_KpInt.subset_interior_iff.2 fun _ hx =>
    Or.inl (Or.inl (image_mono k.KpInt_subset_Kp hx))

theorem p_mem_interior_K : p ∈ interior k.K := by
  refine k.image_KpInt_subset_interior ⟨0, ?_, c.e.hχ0⟩
  refine ⟨by rw [morseNorm_zero]; exact c.ρB_pos, ?_, ?_⟩
  · rw [perpSq, axial_zero, morseNorm_zero]; have := k.hδ; nlinarith [sq_nonneg k.τ]
  · rw [axial_zero]; linarith [k.hδ]

/-- The open core of the pusher support `Kq`. -/
def KqInt : Set (Fin n → ℝ) :=
  {y | uq c.d.hk c.hkq y ^ 2 < c.uB ^ 2 ∧
    ‖posPart c.d.hk y‖ ^ 2 < k.τ ^ 2 * uq c.d.hk c.hkq y ^ 2 + 2 * k.δ ^ 2 ∧
    -k.δ < c.σ * uq c.d.hk c.hkq y}

theorem isOpen_KqInt : IsOpen k.KqInt :=
  (isOpen_lt ((continuous_uq c.d.hk c.hkq).pow 2) continuous_const).inter
    ((isOpen_lt (continuous_normSq_posPart c.d.hk)
      ((continuous_const.mul ((continuous_uq c.d.hk c.hkq).pow 2)).add continuous_const)).inter
      (isOpen_lt continuous_const (continuous_const.mul (continuous_uq c.d.hk c.hkq))))

theorem KqInt_subset_Kq : k.KqInt ⊆ Kq c.d.hk c.hkq k.δ k.τ c.σ c.uB := fun _ hy =>
  ⟨hy.1.le, hy.2.1.le, hy.2.2.le⟩

theorem isOpen_image_KqInt : IsOpen (c.d.χ '' k.KqInt) := by
  refine (c.d.χ.isOpen_image_iff_of_subset_source fun y hy => ?_).2 k.isOpen_KqInt
  exact c.d.hball (k.Kq_subset_ball (k.KqInt_subset_Kq hy))

theorem image_KqInt_subset_interior : c.d.χ '' k.KqInt ⊆ interior k.K :=
  k.isOpen_image_KqInt.subset_interior_iff.2 fun _ hx =>
    Or.inl (Or.inr (image_mono k.KqInt_subset_Kq hx))

theorem q_mem_interior_K : q ∈ interior k.K := by
  refine k.image_KqInt_subset_interior ⟨0, ?_, c.d.hχ0⟩
  refine ⟨by rw [uq_zero]; have := c.uB_pos; nlinarith, ?_, ?_⟩
  · rw [uq_zero, posPart_zero, norm_zero]; have := k.hδ; nlinarith [sq_nonneg k.τ]
  · rw [uq_zero, mul_zero]; linarith [k.hδ]

/-- The open core of the support set `Sσ` of the tube piece. -/
def SσInt : Set M :=
  c.TubeOpenσ ∩ {x | c.c₁ - c.η / 2 < f x ∧ f x < c.c₂ + c.η / 2} ∩
    (c.TubeOpen ∩ c.ζ ⁻¹' {v | ‖v‖ < k.δ'})

theorem isOpen_SσInt : IsOpen k.SσInt :=
  (c.isOpen_TubeOpenσ.inter
    ((isOpen_lt continuous_const c.hfs.continuous).inter
      (isOpen_lt c.hfs.continuous continuous_const))).inter
    (c.continuousOn_ζ.isOpen_inter_preimage c.isOpen_TubeOpen
      (isOpen_lt continuous_norm continuous_const))

theorem SσInt_subset_Sσ : k.SσInt ⊆ k.Sσ := fun _ hx =>
  k.mem_Sσ_iff.2 ⟨hx.1.1, ⟨hx.1.2.1.le, hx.1.2.2.le⟩, hx.2.2.le⟩

theorem SσInt_subset_interior : k.SσInt ⊆ interior k.K :=
  k.isOpen_SσInt.subset_interior_iff.2 fun _ hx => Or.inr (k.SσInt_subset_Sσ hx)

/-- The pusher at `p` vanishes off the interior of `K`. -/
theorem push_Yp'_eq_zero_of_notMem_interior {x : M} (hx : x ∉ interior k.K) :
    c.e.push k.Yp' x = 0 := by
  by_cases hK : x ∈ c.e.χ '' Kp k.δ k.τ c.e₁ c.ρB
  · obtain ⟨y, hy, rfl⟩ := hK
    have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) c.e.R' := k.Kp_subset_ball hy
    rw [MorseChartData.push_apply_chart _ hyb]
    have hY : k.Yp' y = (c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y)) • c.e₁ := rfl
    have hnot : y ∉ k.KpInt := fun h => hx (k.image_KpInt_subset_interior ⟨y, h, rfl⟩)
    have h0 : βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y = 0 := by
      simp only [KpInt, mem_ofPred_eq, not_and, not_lt] at hnot
      by_cases h1 : morseNorm n y < c.ρB
      · by_cases h2 : perpSq c.e₁ y < k.τ ^ 2 * axial c.e₁ y ^ 2 + 2 * k.δ ^ 2
        · rw [βp_eq_zero_of_axial k.hδ (hnot h1 h2), zero_mul]
        · rw [βp_eq_zero_of_perpSq k.hδ (not_lt.1 h2), zero_mul]
      · rw [ψp_eq_zero c.ρA_pos.le c.ρA_lt_ρB (not_lt.1 h1), mul_zero]
    rw [hY, h0, mul_zero, zero_smul]
    exact ContinuousLinearMap.map_zero _
  · exact k.push_Yp'_eq_zero_of_notMem hK

/-- The pusher at `q` vanishes off the interior of `K`. -/
theorem push_Yq'_eq_zero_of_notMem_interior {x : M} (hx : x ∉ interior k.K) :
    c.d.push k.Yq' x = 0 := by
  by_cases hK : x ∈ c.d.χ '' Kq c.d.hk c.hkq k.δ k.τ c.σ c.uB
  · obtain ⟨y, hy, rfl⟩ := hK
    have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) c.d.R' := k.Kq_subset_ball hy
    rw [MorseChartData.push_apply_chart _ hyb]
    have hY : k.Yq' y =
        -(c.σ * c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y)) •
          c.e₀' := rfl
    have hnot : y ∉ k.KqInt := fun h => hx (k.image_KqInt_subset_interior ⟨y, h, rfl⟩)
    have h0 : βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y = 0 := by
      simp only [KqInt, mem_ofPred_eq, not_and, not_lt] at hnot
      by_cases h1 : uq c.d.hk c.hkq y ^ 2 < c.uB ^ 2
      · by_cases h2 : ‖posPart c.d.hk y‖ ^ 2 < k.τ ^ 2 * uq c.d.hk c.hkq y ^ 2 + 2 * k.δ ^ 2
        · rw [βq_eq_zero_of_uq c.d.hk c.hkq k.hδ (hnot h1 h2), zero_mul]
        · rw [βq_eq_zero_of_posPart c.d.hk c.hkq k.hδ (not_lt.1 h2), zero_mul]
      · rw [ψq_eq_zero c.d.hk c.hkq c.uA_pos.le c.uA_lt_uB (not_lt.1 h1), mul_zero]
    rw [hY, h0, mul_zero, neg_zero, zero_smul]
    exact ContinuousLinearMap.map_zero _
  · exact k.push_Yq'_eq_zero_of_notMem hK

/-- The tube piece vanishes off the interior of `K`. -/
theorem Ym_eq_zero_of_notMem_interior {x : M} (hx : x ∉ interior k.K) : k.Ym x = 0 := by
  by_cases hS : x ∈ k.Sσ
  · obtain ⟨hT, hf, hζ⟩ := k.mem_Sσ_iff.1 hS
    rw [k.Ym_of_mem hT]
    apply k.YmFun_eq_zero_of
    have hnot : x ∉ k.SσInt := fun h => hx (k.SσInt_subset_interior h)
    have hlo := c.c₁_sub_half_lt_lo₁
    have hhi := c.hi₂_lt_c₂_add_half
    by_cases h1 : c.c₁ - c.η / 2 < f x
    · by_cases h2 : f x < c.c₂ + c.η / 2
      · have h3 : ¬ ‖c.ζ x‖ < k.δ' := fun h3 => hnot ⟨⟨hT, h1, h2⟩, hT.1, h3⟩
        have hβ : k.βm' x = 0 :=
          cut_eq_zero k.two_δ_sq_lt_δ'_sq (pow_le_pow_left₀ k.δ'_pos.le (not_lt.1 h3) 2)
        rw [hβ, zero_mul]
      · have hψ : c.ψm' x = 0 := plateau_eq_zero_of_ge hhi (by linarith [not_lt.1 h2])
        rw [hψ, mul_zero]
    · have hψ : c.ψm' x = 0 := plateau_eq_zero_of_le hlo (not_lt.1 h1)
      rw [hψ, mul_zero]
  · exact k.Ym_eq_zero_of_notMem_Sσ hS

/-- **Off the interior of `K`, the modified field is the original one.** -/
theorem V'_eq_V_of_notMem_interior {x : M} (hx : x ∉ interior k.K) : k.V' x = c.D.V x := by
  rw [V'_apply, k.push_Yp'_eq_zero_of_notMem_interior hx, k.push_Yq'_eq_zero_of_notMem_interior hx,
    k.Ym_eq_zero_of_notMem_interior hx, add_zero, add_zero, add_zero]

/-- Off the interior of `K` and in the strip, `f` strictly decreases along `V'`. -/
theorem dfV_V'_neg_of_notMem_interior {x : M} (hx : f x ∈ Icc a' b') (hx' : x ∉ interior k.K) :
    dfV I f k.V' x < 0 := by
  unfold dfV
  rw [k.V'_eq_V_of_notMem_interior hx']
  refine c.D.neg x hx ?_
  rw [mem_pair_iff]
  rintro (rfl | rfl)
  · exact hx' k.p_mem_interior_K
  · exact hx' k.q_mem_interior_K

/-! ### The off-`K` phase -/

/-- **The off-`K` phase**: a trajectory starting in the strip reaches the level `a'` or enters
`K`, staying off `K` and above `a'` before. -/
theorem exists_hit_K_or_bottom {x : M} (hx : f x ∈ Icc a' b') :
    ∃ t, 0 ≤ t ∧ (k.Φ t x ∈ k.K ∨ f (k.Φ t x) ≤ a') ∧
      ∀ s ∈ Ico 0 t, k.Φ s x ∉ k.K ∧ a' < f (k.Φ s x) := by
  by_cases hxK : x ∈ interior k.K
  · exact ⟨0, le_rfl, Or.inl (by rw [k.Φ_zero]; exact interior_subset hxK),
      fun s hs => absurd hs.2 (not_lt.2 hs.1)⟩
  set C₀ : Set M := f ⁻¹' Icc a' b' ∩ (interior k.K)ᶜ with hC₀
  have hC₀c : IsCompact C₀ := c.hf.compact.inter_right isOpen_interior.isClosed_compl
  have hxC : x ∈ C₀ := ⟨hx, hxK⟩
  obtain ⟨t, ht, hexit⟩ := k.exists_exit_of_deriv_pos hC₀c (L := fun y => -f y)
    c.hfs.continuous.neg.continuousOn (fun y hy => by
      refine ⟨-dfV I f k.V' y, by linarith [k.dfV_V'_neg_of_notMem_interior hy.1 hy.2], ?_⟩
      have := (k.hasDerivAt_f_Φ y 0).neg
      rwa [k.Φ_zero] at this) x hxC
  set F : Set M := k.K ∪ f ⁻¹' Iic a' with hF
  have hFc : IsClosed F := k.isClosed_K.union (isClosed_Iic.preimage c.hfs.continuous)
  have hhit : ∃ s ∈ Icc 0 t, k.Φ s x ∈ F := by
    by_contra h
    push Not at h
    have havoid : ∀ s ∈ Ico 0 t, k.Φ s x ∉ k.K := fun s hs h' =>
      h s (Ico_subset_Icc_self hs) (Or.inl h')
    have heq := k.flow_eq_Φ_of_avoid havoid t (right_mem_Icc.2 ht)
    apply hexit
    refine ⟨⟨?_, ?_⟩, fun h' => h t (right_mem_Icc.2 ht) (Or.inl (interior_subset h'))⟩
    · by_contra hlt
      exact h t (right_mem_Icc.2 ht) (Or.inr (le_of_lt (not_le.1 hlt)))
    · rw [← heq]; exact (f_flow_le c.hfs x ht).trans hx.2
  obtain ⟨s₀, hs₀, hs₀F, hmin⟩ := exists_first_time hFc (k.continuous_Φ_curve x) hhit
  refine ⟨s₀, hs₀.1, ?_, fun s hs => ?_⟩
  · rcases hs₀F with h | h
    · exact Or.inl h
    · exact Or.inr h
  · have := hmin s hs
    simp only [hF, mem_union, mem_preimage, mem_Iic, not_or, not_le] at this
    exact this

/-! ### The ball of `p` -/

/-- **The ball of `p` feeds the middle band through `Wp2`**: every trajectory starting in `Wball`
reaches a point of `Wp2 ∩ Tmid` at the level `lo₂`. -/
theorem exists_reach_Wp2_Tmid (hk : k.Good) {x : M} (hx : x ∈ c.Wball) :
    ∃ t, 0 ≤ t ∧ k.Φ t x ∈ k.Wp2 ∧ k.Φ t x ∈ k.Tmid ∧ f (k.Φ t x) = c.lo₂ := by
  have hx' := (k.Wball_eq_union ▸ hx : x ∈ k.Wp1 ∪ k.Wp2)
  rcases hx' with hx1 | hx2
  · obtain ⟨t₁, ht₁, hW2, -⟩ := k.exists_reach_Wp2 hk.hζmin hx1
    obtain ⟨t₂, ht₂, hT, hf, hW⟩ := k.exists_reach_Tmid_of_mem_Wp2 hW2
    refine ⟨t₁ + t₂, by positivity, ?_, ?_, ?_⟩
    · rw [k.Φ_add]; exact hW t₂ (right_mem_Icc.2 ht₂)
    · rw [k.Φ_add]; exact hT
    · rw [k.Φ_add]; exact hf
  · obtain ⟨t₂, ht₂, hT, hf, hW⟩ := k.exists_reach_Tmid_of_mem_Wp2 hx2
    exact ⟨t₂, ht₂, hW t₂ (right_mem_Icc.2 ht₂), hT, hf⟩

/-! ### The middle band -/

/-- On a segment in the one-sided tube at the middle levels, `‖ζ‖²` is antitone. -/
theorem antitoneOn_normSq_ζ_Φ_of_band {x : M} {t₀ t₁ : ℝ}
    (h : ∀ s ∈ Icc t₀ t₁, k.Φ s x ∈ c.TubeOpenσ ∧ c.lo₂ ≤ f (k.Φ s x) ∧ f (k.Φ s x) ≤ c.hi₁) :
    AntitoneOn (fun s => ‖c.ζ (k.Φ s x)‖ ^ 2) (Icc t₀ t₁) := by
  refine antitoneOn_Icc_of_hasDerivAt_nonpos
    (g' := fun s => -(4 * (c.lam * k.βm' (k.Φ s x))) * ‖c.ζ (k.Φ s x)‖ ^ 2)
    (fun s hs => k.hasDerivAt_normSq_ζ_Φ_mid' (h s hs).1 (h s hs).2.1 (h s hs).2.2)
    (fun s _ => ?_)
  have := k.βm'_nonneg (k.Φ s x)
  have := c.lam_pos
  have : 0 ≤ 4 * (c.lam * k.βm' (k.Φ s x)) * ‖c.ζ (k.Φ s x)‖ ^ 2 := by positivity
  linarith

/-- A band segment starting with `‖ζ‖ ≤ δ'` lies in `Tmid`. -/
theorem Φ_mem_Tmid_of_band {x : M} (hζ : ‖c.ζ x‖ ≤ k.δ') {t : ℝ}
    (h : ∀ s ∈ Icc 0 t, k.Φ s x ∈ c.TubeOpenσ ∧ c.lo₂ ≤ f (k.Φ s x) ∧ f (k.Φ s x) ≤ c.hi₁) :
    ∀ s ∈ Icc 0 t, k.Φ s x ∈ k.Tmid := by
  intro s hs
  have hanti := k.antitoneOn_normSq_ζ_Φ_of_band h
  have h1 : ‖c.ζ (k.Φ s x)‖ ^ 2 ≤ ‖c.ζ (k.Φ 0 x)‖ ^ 2 :=
    hanti (left_mem_Icc.2 (hs.1.trans hs.2)) hs hs.1
  rw [k.Φ_zero] at h1
  have hζs : ‖c.ζ (k.Φ s x)‖ ≤ k.δ' := by
    have h2 : ‖c.ζ (k.Φ s x)‖ ^ 2 ≤ k.δ' ^ 2 :=
      h1.trans (pow_le_pow_left₀ (norm_nonneg _) hζ 2)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.δ'_pos.le two_ne_zero).1 h2
  obtain ⟨hT, hf1, hf2⟩ := h s hs
  refine ⟨k.mem_Sσ_iff.2 ⟨hT, ⟨?_, ?_⟩, hζs⟩, hf1, hf2⟩
  · linarith [c.lo₂_mem_levels]
  · linarith [c.hi₁_mem_levels]

/-- `ζ` vanishes along a band segment once it vanishes at its start. -/
theorem ζ_eq_zero_of_band {x : M} (hζ : c.ζ x = 0) {t : ℝ}
    (h : ∀ s ∈ Icc 0 t, k.Φ s x ∈ c.TubeOpenσ ∧ c.lo₂ ≤ f (k.Φ s x) ∧ f (k.Φ s x) ≤ c.hi₁) :
    ∀ s ∈ Icc 0 t, c.ζ (k.Φ s x) = 0 := by
  intro s hs
  have hanti := k.antitoneOn_normSq_ζ_Φ_of_band h
  have h1 : ‖c.ζ (k.Φ s x)‖ ^ 2 ≤ ‖c.ζ (k.Φ 0 x)‖ ^ 2 :=
    hanti (left_mem_Icc.2 (hs.1.trans hs.2)) hs hs.1
  rw [k.Φ_zero, hζ, norm_zero] at h1
  have h2 : ‖c.ζ (k.Φ s x)‖ ^ 2 = 0 := le_antisymm (by simpa using h1) (by positivity)
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

/-- A short forward band segment from a point of the one-sided tube at a level `< hi₁`, whose
level moves up initially. -/
theorem exists_band_segment_up {x : M} (hT : x ∈ c.TubeOpenσ) (hlo : c.lo₂ ≤ f x)
    (hhi : f x < c.hi₁) (hd : 0 < -1 + 2 * k.βm x) :
    ∃ t, 0 < t ∧ (∀ s ∈ Icc 0 t, k.Φ s x ∈ c.TubeOpenσ ∧ c.lo₂ ≤ f (k.Φ s x) ∧
      f (k.Φ s x) ≤ c.hi₁) ∧ (∀ s ∈ Ioc 0 t, f x < f (k.Φ s x)) ∧ f (k.Φ t x) < c.hi₁ := by
  obtain ⟨ε₁, hε₁, hO₁⟩ := k.exists_Icc_Φ_mem_open c.isOpen_TubeOpenσ (t := 0) (x := x)
    (by rw [k.Φ_zero]; exact hT)
  obtain ⟨ε₂, hε₂, hO₂⟩ := k.exists_Icc_Φ_mem_open (isOpen_lt c.hfs.continuous continuous_const)
    (t := 0) (x := x) (O := {y | f y < c.hi₁}) (by rw [k.Φ_zero]; exact hhi)
  have hder : HasDerivAt (fun s => f (k.Φ s x)) (-1 + 2 * k.βm x) 0 := by
    have := k.hasDerivAt_f_Φ_mid hT hlo hhi.le
    exact this
  have hev := eventually_gt_of_hasDerivAt_pos hd hder
  rw [k.Φ_zero] at hev
  obtain ⟨ε₃, hε₃, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  have hε₃' : 0 < ε₃ := hε₃
  refine ⟨min (min ε₁ ε₂) ε₃, lt_min (lt_min hε₁ hε₂) hε₃', fun s hs => ?_, fun s hs => ?_, ?_⟩
  · have hs1 : s ≤ ε₁ := hs.2.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hs2 : s ≤ ε₂ := hs.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hs3 : s ≤ ε₃ := hs.2.trans (min_le_right _ _)
    refine ⟨hO₁ s ⟨by linarith [hs.1], by linarith⟩, ?_,
      (hO₂ s ⟨by linarith [hs.1], by linarith⟩).le⟩
    rcases hs.1.eq_or_lt with h | h
    · rw [← h, k.Φ_zero]; exact hlo
    · exact hlo.trans (hsub ⟨h, hs3⟩).le
  · exact hsub ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
  · exact hO₂ _ ⟨by linarith [lt_min (lt_min hε₁ hε₂) hε₃'],
      by linarith [min_le_left (min ε₁ ε₂) ε₃, min_le_right ε₁ ε₂]⟩

/-- A short forward band segment from a point of the one-sided tube at a level `> lo₂`, whose
level moves down initially. -/
theorem exists_band_segment_down {x : M} (hT : x ∈ c.TubeOpenσ) (hlo : c.lo₂ < f x)
    (hhi : f x ≤ c.hi₁) (hd : -1 + 2 * k.βm x < 0) :
    ∃ t, 0 < t ∧ (∀ s ∈ Icc 0 t, k.Φ s x ∈ c.TubeOpenσ ∧ c.lo₂ ≤ f (k.Φ s x) ∧
      f (k.Φ s x) ≤ c.hi₁) ∧ (∀ s ∈ Ioc 0 t, f (k.Φ s x) < f x) ∧ c.lo₂ < f (k.Φ t x) := by
  obtain ⟨ε₁, hε₁, hO₁⟩ := k.exists_Icc_Φ_mem_open c.isOpen_TubeOpenσ (t := 0) (x := x)
    (by rw [k.Φ_zero]; exact hT)
  obtain ⟨ε₂, hε₂, hO₂⟩ := k.exists_Icc_Φ_mem_open (isOpen_lt continuous_const c.hfs.continuous)
    (t := 0) (x := x) (O := {y | c.lo₂ < f y}) (by rw [k.Φ_zero]; exact hlo)
  have hder : HasDerivAt (fun s => f (k.Φ s x)) (-1 + 2 * k.βm x) 0 :=
    k.hasDerivAt_f_Φ_mid hT hlo.le hhi
  have hev := eventually_lt_of_hasDerivAt_neg hd hder
  rw [k.Φ_zero] at hev
  obtain ⟨ε₃, hε₃, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  have hε₃' : 0 < ε₃ := hε₃
  refine ⟨min (min ε₁ ε₂) ε₃, lt_min (lt_min hε₁ hε₂) hε₃', fun s hs => ?_, fun s hs => ?_, ?_⟩
  · have hs1 : s ≤ ε₁ := hs.2.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hs2 : s ≤ ε₂ := hs.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hs3 : s ≤ ε₃ := hs.2.trans (min_le_right _ _)
    refine ⟨hO₁ s ⟨by linarith [hs.1], by linarith⟩, (hO₂ s ⟨by linarith [hs.1], by linarith⟩).le,
      ?_⟩
    rcases hs.1.eq_or_lt with h | h
    · rw [← h, k.Φ_zero]; exact hhi
    · exact (hsub ⟨h, hs3⟩).le.trans hhi
  · exact hsub ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
  · exact hO₂ _ ⟨by linarith [lt_min (lt_min hε₁ hε₂) hε₃'],
      by linarith [min_le_left (min ε₁ ε₂) ε₃, min_le_right ε₁ ε₂]⟩

/-- **The arc reaches the level `hi₁`**: a point of `Tmid` with `ζ = 0` moves up to the level
`hi₁`, staying on the arc. -/
theorem exists_reach_hi₁_of_ζ_eq_zero {x : M} (hx : x ∈ k.Tmid) (hζ : c.ζ x = 0) :
    ∃ t, 0 ≤ t ∧ k.Φ t x ∈ k.Tmid ∧ f (k.Φ t x) = c.hi₁ ∧ c.ζ (k.Φ t x) = 0 := by
  have hT := k.Tmid_subset_TubeOpenσ hx
  rcases hx.2.2.eq_or_lt with hhi | hhi
  · exact ⟨0, le_rfl, by rw [k.Φ_zero]; exact hx, by rw [k.Φ_zero]; exact hhi,
      by rw [k.Φ_zero]; exact hζ⟩
  -- step 1: a short segment up, staying on the arc
  have hβ : k.βm x = 1 := k.βm_eq_one_of_ζ_eq_zero hζ
  obtain ⟨ε, hε, hband, hup, hεhi⟩ := k.exists_band_segment_up hT hx.2.1 hhi (by rw [hβ]; norm_num)
  have hζε := k.ζ_eq_zero_of_band hζ hband
  have hTmidε := k.Φ_mem_Tmid_of_band (by rw [hζ, norm_zero]; exact k.δ'_pos.le) hband
  set x₁ := k.Φ ε x with hx₁
  have hx₁T : x₁ ∈ k.Tmid := hTmidε ε (right_mem_Icc.2 hε.le)
  have hx₁ζ : c.ζ x₁ = 0 := hζε ε (right_mem_Icc.2 hε.le)
  have hx₁lo : c.lo₂ < f x₁ := lt_of_le_of_lt hx.2.1 (hup ε ⟨hε, le_rfl⟩)
  -- step 2: the mid-band exit from `x₁` is at `hi₁`
  obtain ⟨t, ht, hall, -, hexit⟩ := k.exists_exit_mid_band hx₁T
  have hband' : ∀ s ∈ Icc 0 t, k.Φ s x₁ ∈ c.TubeOpenσ ∧ c.lo₂ ≤ f (k.Φ s x₁) ∧
      f (k.Φ s x₁) ≤ c.hi₁ := fun s hs =>
    ⟨k.Tmid_subset_TubeOpenσ (hall s hs), (hall s hs).2.1, (hall s hs).2.2⟩
  have hζt := k.ζ_eq_zero_of_band hx₁ζ hband'
  -- `f` is monotone along the arc segment
  have hmono : MonotoneOn (fun s => f (k.Φ s x₁)) (Icc 0 t) := by
    refine monotoneOn_Icc_of_hasDerivAt_nonneg (g' := fun s => -1 + 2 * k.βm (k.Φ s x₁))
      (fun s hs => k.hasDerivAt_f_Φ_mid' (hband' s hs).1 (hband' s hs).2.1 (hband' s hs).2.2)
      (fun s hs => ?_)
    rw [k.βm_eq_one_of_ζ_eq_zero (hζt s hs)]; norm_num
  have hft : f x₁ ≤ f (k.Φ t x₁) := by
    have h1 : f (k.Φ 0 x₁) ≤ f (k.Φ t x₁) := hmono (left_mem_Icc.2 ht) (right_mem_Icc.2 ht) ht
    rwa [k.Φ_zero] at h1
  have hfhi : f (k.Φ t x₁) = c.hi₁ := by
    rcases hexit with h | h
    · exact h.1
    · exfalso; linarith
  refine ⟨ε + t, by positivity, ?_, ?_, ?_⟩
  · rw [k.Φ_add]; exact hall t (right_mem_Icc.2 ht)
  · rw [k.Φ_add]; exact hfhi
  · rw [k.Φ_add]; exact hζt t (right_mem_Icc.2 ht)

/-- **A band point with `‖ζ‖ ≥ 2δ` above `lo₂` moves strictly down**, staying in `Tmid`. -/
theorem exists_pos_mem_Tmid_of_two_δ_le {x : M} (hx : x ∈ k.Tmid) (hζ : 2 * k.δ ≤ ‖c.ζ x‖)
    (hlo : c.lo₂ < f x) :
    ∃ t, 0 < t ∧ k.Φ t x ∈ k.Tmid ∧ f (k.Φ t x) < f x ∧ c.lo₂ < f (k.Φ t x) := by
  have hT := k.Tmid_subset_TubeOpenσ hx
  have hβ : k.βm x = 0 :=
    cut_eq_zero k.δ_sq_lt_two_δ_sq (pow_le_pow_left₀ (by linarith [k.hδ]) hζ 2)
  obtain ⟨ε, hε, hband, hdown, hεlo⟩ :=
    k.exists_band_segment_down hT hlo hx.2.2 (by rw [hβ]; norm_num)
  have hTmidε := k.Φ_mem_Tmid_of_band (k.norm_ζ_le_of_mem_Sσ hx.1) hband
  exact ⟨ε, hε, hTmidε ε (right_mem_Icc.2 hε.le), hdown ε ⟨hε, le_rfl⟩, hεlo⟩

end CancelConsts

end CancelData

end GradientLikeStrip

end

end PoincareHighDim
