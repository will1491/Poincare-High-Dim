import Submission.Morse.Cancellation.Flow.CancelFlowQ

/-!
# Cancellation, step C4c (Q, continued): exits from the region of `q` and the terminal descent

For `k : c.CancelConsts` and `hk : k.Good` this module provides

* **the faces of the region of `q`** (`Fq = FqLow ∪ {f ≤ hi₁}`): the region `Rq` is forward
  invariant until a face is hit (`Φ_mem_Rq_until`), hence every trajectory leaves it through the
  lower face `σ u = -2δ` or through the level `hi₁` (`exists_exit_Rq_face`); at the level `hi₁`
  the exit point has `σ u ≥ uB` and lies in the one-sided tube (`hi₁_face`), and from the upper
  region `RqPos` the exit at `hi₁` lands in `Tmid ∩ RqPos` (`exists_exit_RqPos_face`);
* **the terminal descent** (`exists_f_le_a'_of_face`): from the lower face the trajectory descends
  below `a'` along the original field (the model exit lemma `exists_exit_mem_leftTube` brings it
  to the level `f q - ε` in a left tube around the other arm, avoiding `K` since `σ u ≤ -2δ` and
  the segment is outside the basin of `p`; the hypothesis `harm` finishes);
* **the lower region** `RqNeg` (`-2δ ≤ σ u ≤ 0`): forward invariant until the lower face, left
  by LaSalle (`σ u` / `-‖v‖²`), hence descending below `a'` (`exists_f_le_a'_of_mem_RqNeg`);
* **the axis segment** `Ax` (`v = 0`, `0 ≤ σ u`, `u² ≤ uB²`): forward invariant until `σ u = 0`,
  reaching `q` (`exists_reach_q_of_mem_Ax`) and then descending below `a'`
  (`exists_f_le_a'_of_mem_Ax`);
* **the classification of `K`** (`mem_K_cases`: `Wball`, `Tmid` or `Rq`) with
  `Sσ_high_subset_RqPos`, and `notMem_basin_of_f_lt`.

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

variable [DecidableEq M] {a' b' : ℝ} {p q : M} (c : CancelData I f a' b' p q)

/-! ### Points descending below `a'` are not in the basin of `p` -/

/-- A point whose forward trajectory drops below `a'` is not in the basin of `p`. -/
theorem notMem_basin_of_f_lt {x : M} {T : ℝ} (hf : f (c.D.flow T x) < a') :
    x ∉ c.D.basin p c.hp := by
  rintro ⟨t, ht, hmem⟩
  have hfp := c.f_p_mem.1
  have hball : ∀ z ∈ c.e.χ '' {y | morseNorm n y < c.D.rm p c.hp}, f p ≤ f z := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : morseNorm n y < c.D.rm p c.hp := hy
    rw [c.f_chart_p (hy'.le.trans (c.D.hrm p c.hp).2)]
    nlinarith [sq_nonneg (morseNorm n y)]
  rcases le_or_gt t T with h | h
  · have := flow_mem_modelBall_of_index_zero (D := c.D) c.hkp hmem (t := T - t) (by linarith)
    rw [flow_flow, add_sub_cancel] at this
    linarith [hball _ this]
  · have h1 := f_flow_le c.hfs (D := c.D) (c.D.flow T x) (t := t - T) (by linarith)
    rw [flow_flow, add_sub_cancel] at h1
    linarith [hball _ hmem]

/-- The chart point of `q` of a point of `qBall'`, with the bound `‖y‖ ≤ R`. -/
theorem symm_mem_source_of_sq_le {y : Fin n → ℝ} (hy : morseNorm n y ^ 2 ≤ 3 * c.ε) :
    c.d.χ.symm (c.d.χ y) = y := by
  refine c.d.χ.left_inv (c.d.hsrc y ?_)
  have h1 : morseNorm n y ≤ Real.sqrt (3 * c.ε) := Real.le_sqrt_of_sq_le hy
  exact h1.trans (c.sqrt_three_ε_lt_rmq.le.trans (c.D.hrm q c.hq).2)

/-- The middle face `σ u ≤ 0` of the region of `q`. -/
def FqMid : Set M :=
  c.d.χ '' {y | morseNorm n y ^ 2 ≤ 3 * c.ε ∧ c.σ * uq c.d.hk c.hkq y ≤ 0}

theorem isCompact_image_of_le {S : Set (Fin n → ℝ)} (hS : IsClosed S)
    (hsub : S ⊆ {y | morseNorm n y ^ 2 ≤ 3 * c.ε}) : IsCompact (c.d.χ '' S) := by
  refine c.d.isCompact_image_of_subset ?_ c.sqrt_three_ε_lt_R'q fun y hy =>
    Real.le_sqrt_of_sq_le (hsub hy)
  exact (isCompact_morseNorm_le (Real.sqrt (3 * c.ε))).of_isClosed_subset hS
    fun y hy => Real.le_sqrt_of_sq_le (hsub hy)

/-- An open neighbourhood condition in the ball of `q`. -/
theorem isOpen_qBall'_inter {P : ℝ → Prop} (hP : IsOpen {r | P r}) :
    IsOpen (c.qBall' ∩ {x | P (c.σ * uq c.d.hk c.hkq (c.d.χ.symm x))}) :=
  c.continuousOn_symm_qBall'.isOpen_inter_preimage c.isOpen_qBall'
    (hP.preimage (continuous_const.mul (continuous_uq c.d.hk c.hkq)))

/-- The axis segment `v = 0`, `0 ≤ σ u`, `u² ≤ uB²` of the upper region. -/
def AxSet : Set (Fin n → ℝ) :=
  {y | posPart c.d.hk y = 0 ∧ 0 ≤ c.σ * uq c.d.hk c.hkq y ∧ uq c.d.hk c.hkq y ^ 2 ≤ c.uB ^ 2}

/-- The axis segment of the upper region of `q`. -/
def Ax : Set M := c.d.χ '' c.AxSet

theorem isClosed_AxSet : IsClosed c.AxSet :=
  (isClosed_eq c.d.continuous_posPart continuous_const).inter
    ((isClosed_le continuous_const (continuous_const.mul (continuous_uq c.d.hk c.hkq))).inter
      (isClosed_le ((continuous_uq c.d.hk c.hkq).pow 2) continuous_const))

theorem isClosed_FqMid : IsClosed c.FqMid :=
  (c.isCompact_image_of_le ((isClosed_le (continuous_morseNorm.pow 2) continuous_const).inter
    (isClosed_le (continuous_const.mul (continuous_uq c.d.hk c.hkq)) continuous_const))
    fun _ hy => hy.1).isClosed

theorem σ_uq_le_of_mem_FqMid {x : M} (hx : x ∈ c.FqMid) :
    c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) ≤ 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.symm_mem_source_of_sq_le hy.1]; exact hy.2

theorem mem_FqMid_of {x : M} (hx : x ∈ c.qBall')
    (h : c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) ≤ 0) : x ∈ c.FqMid :=
  c.d.mem_image_of_symm_mem (c.qBall'_subset_image_ball hx)
    ⟨(c.symm_sq_lt_of_mem_qBall' hx).le, h⟩

theorem mem_Ax_of_symm {x : M} (hx : x ∈ c.qBall') (h : c.d.χ.symm x ∈ c.AxSet) : x ∈ c.Ax :=
  c.d.mem_image_of_symm_mem (c.qBall'_subset_image_ball hx) h

namespace CancelConsts

variable {c} (k : c.CancelConsts)

/-! ### The faces of the region of `q` -/

/-- The lower face `σ u ≤ -2δ` of the region of `q` (as a closed set of `M`). -/
def FqLow : Set M :=
  c.d.χ '' {y | morseNorm n y ^ 2 ≤ 3 * c.ε ∧ c.σ * uq c.d.hk c.hkq y ≤ -(2 * k.δ)}

theorem isClosed_FqLow : IsClosed k.FqLow :=
  (c.isCompact_image_of_le ((isClosed_le (continuous_morseNorm.pow 2) continuous_const).inter
    (isClosed_le (continuous_const.mul (continuous_uq c.d.hk c.hkq)) continuous_const))
    fun _ hy => hy.1).isClosed

theorem σ_uq_le_of_mem_FqLow {x : M} (hx : x ∈ k.FqLow) :
    c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) ≤ -(2 * k.δ) := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.symm_mem_source_of_sq_le hy.1]; exact hy.2

theorem mem_FqLow_of {x : M} (hx : x ∈ c.qBall')
    (h : c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) ≤ -(2 * k.δ)) : x ∈ k.FqLow :=
  c.d.mem_image_of_symm_mem (c.qBall'_subset_image_ball hx)
    ⟨(c.symm_sq_lt_of_mem_qBall' hx).le, h⟩

/-- The exit faces of the region of `q`: the lower face and the level `hi₁`. -/
def Fq : Set M := k.FqLow ∪ {x | f x ≤ c.hi₁}

theorem isClosed_Fq : IsClosed k.Fq :=
  k.isClosed_FqLow.union (isClosed_le c.hfs.continuous continuous_const)

/-- **The region of `q` is forward invariant until one of its faces is hit.** -/
theorem Φ_mem_Rq_until (hk : k.Good) {x : M} (hx : x ∈ k.Rq) {t : ℝ}
    (hF : ∀ s ∈ Icc 0 t, k.Φ s x ∉ k.Fq) : ∀ s ∈ Icc 0 t, k.Φ s x ∈ k.Rq := by
  have hQ : IsClosed {s : ℝ | k.Φ s x ∈ k.Rq} :=
    (k.isCompact_Rq hk).isClosed.preimage (k.continuous_Φ_curve x)
  refine Icc_subset_of_isClosed_of_step hQ (by simp [hx]) fun s hs hIcc => ?_
  have hsR : k.Φ s x ∈ k.Rq := hIcc (right_mem_Icc.2 hs.1)
  have hsq : k.Φ s x ∈ c.qBall' := k.Rq_subset_qBall' hk hsR
  have hsF := hF s (Ico_subset_Icc_self hs)
  simp only [Fq, mem_union, mem_ofPred_eq, not_or, not_le] at hsF
  have hsu : -(2 * k.δ) < c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s x)) := by
    by_contra h
    exact hsF.1 (k.mem_FqLow_of hsq (not_lt.1 h))
  have hO : k.Φ s x ∈ c.qBall' ∩ {w | -(2 * k.δ) < c.σ * uq c.d.hk c.hkq (c.d.χ.symm w)} ∩
      {w | c.hi₁ < f w} := ⟨⟨hsq, hsu⟩, hsF.2⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open
    ((c.isOpen_qBall'_inter (P := fun r => -(2 * k.δ) < r) (isOpen_lt continuous_const
      continuous_id)).inter (isOpen_lt continuous_const c.hfs.continuous)) hO
  refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (s + ε) t, lt_min (by linarith) hs.2,
    fun s' hs' => ?_⟩
  have hs'ε : s' ≤ s + ε := hs'.2.trans (min_le_left _ _)
  have hall : ∀ u ∈ Icc s s', k.Φ u x ∈ c.qBall' := fun u hu =>
    (hεO u ⟨by linarith [hu.1], hu.2.trans hs'ε⟩).1.1
  obtain ⟨⟨hs'q, hs'u⟩, hs'f⟩ := hεO s' ⟨by linarith [hs'.1], hs'ε⟩
  have hs'f' : c.hi₁ < f (k.Φ s' x) := hs'f
  have hy := k.symm_mem_RegQ_of_mem_Rq hk hsR
  refine k.mem_Rq_of_symm hs'q ⟨hs'u.le, ?_, ?_⟩
  · rw [← c.hi₁_le_iff (c.morseNorm_le_R_of_sq_lt (k.symm_Φ_q_sq_lt hs'q)),
      c.d.symm_image_eq (c.qBall'_subset_image_ball hs'q)]
    exact hs'f'.le
  · have hanti := k.antitoneOn_normSq_posPart_Φ hall
    have h1 : ‖posPart c.d.hk (c.d.χ.symm (k.Φ s' x))‖ ^ 2 ≤
        ‖posPart c.d.hk (c.d.χ.symm (k.Φ s x))‖ ^ 2 :=
      hanti (left_mem_Icc.2 hs'.1.le) (right_mem_Icc.2 hs'.1.le) hs'.1.le
    have h2 : ‖posPart c.d.hk (c.d.χ.symm (k.Φ s x))‖ ^ 2 ≤ k.ν ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hy.2.2 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.ν_pos.le two_ne_zero).1 (h1.trans h2)

/-- **Exit from the region of `q` through a face**: the lower face `σ u = -2δ` or the level
`hi₁`. -/
theorem exists_exit_Rq_face (hk : k.Good) {x : M} (hx : x ∈ k.Rq) :
    ∃ t, 0 ≤ t ∧ (∀ s ∈ Icc 0 t, k.Φ s x ∈ k.Rq) ∧ (∀ s ∈ Ico 0 t, k.Φ s x ∉ k.Fq) ∧
      (c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ t x)) = -(2 * k.δ) ∨ f (k.Φ t x) = c.hi₁) := by
  obtain ⟨t, ht, hexit⟩ := k.exists_exit_Rq hk x hx
  obtain ⟨t₁, ht₁, -, ht₁F, hall, hbefore⟩ := k.exists_first_hit_face (k.isCompact_Rq hk).isClosed
    k.isClosed_Fq hx (fun t hF => k.Φ_mem_Rq_until hk hx hF) ht hexit
  refine ⟨t₁, ht₁, hall, hbefore, ?_⟩
  have ht₁R := hall t₁ (right_mem_Icc.2 ht₁)
  rcases ht₁F with h | h
  · left
    exact le_antisymm (k.σ_uq_le_of_mem_FqLow h) (k.symm_mem_RegQ_of_mem_Rq hk ht₁R).1
  · right
    exact le_antisymm h (k.hi₁_le_f_of_mem_Rq hk ht₁R)

theorem two_δ_lt_uB : 2 * k.δ < c.uB := by
  have h2 := k.δ_sq_lt
  have h3 : c.ε / 2 ≤ c.ε₂ := by unfold ε₂; nlinarith [sq_nonneg c.d.r₀]
  have h4 := c.uB_sq
  have h5 := c.η_pos
  have : (2 * k.δ) ^ 2 < c.uB ^ 2 := by nlinarith
  exact (pow_lt_pow_iff_left₀ (by linarith [k.hδ]) c.uB_pos.le two_ne_zero).1 this

/-- **The upper face**: at the level `hi₁`, a point of the region of `q` has `σ u ≥ uB > 0` and
lies in the one-sided tube. -/
theorem hi₁_face (hk : k.Good) {y : Fin n → ℝ} (hy : y ∈ k.RegQ) (hf : f (c.d.χ y) = c.hi₁) :
    c.uB ≤ c.σ * uq c.d.hk c.hkq y ∧ c.d.χ y ∈ c.TubeOpenσ := by
  have hsq := k.sq_lt_of_mem_RegQ hk hy
  have hyR := c.morseNorm_le_R_of_sq_lt hsq
  have h1 := c.f_chart_q hyR
  have h2 := c.uB_sq_eq
  have hu2 : c.uB ^ 2 ≤ uq c.d.hk c.hkq y ^ 2 := by nlinarith [sq_nonneg ‖posPart c.d.hk y‖]
  have hσ2 := c.σ_sq
  have huB := c.uB_pos
  have h2δ := k.two_δ_lt_uB
  have hσu2 : c.uB ^ 2 ≤ (c.σ * uq c.d.hk c.hkq y) ^ 2 := by
    rw [mul_pow]; nlinarith
  have habs : c.uB ≤ |c.σ * uq c.d.hk c.hkq y| := by
    rw [← sq_le_sq₀ huB.le (abs_nonneg _), sq_abs]; exact hσu2
  have hpos : c.uB ≤ c.σ * uq c.d.hk c.hkq y := by
    rcases le_or_gt 0 (c.σ * uq c.d.hk c.hkq y) with h | h
    · rwa [abs_of_nonneg h] at habs
    · rw [abs_of_neg h] at habs; linarith [hy.1]
  refine ⟨hpos, c.mem_TubeOpenσ_of_σ_uq_pos hsq ⟨?_, ?_⟩ (huB.trans_le hpos)⟩
  · rw [hf]; have h := c.lo₂_lt_hi₁; have hη := c.η_pos; unfold lo₂ at h; linarith
  · rw [hf]; unfold hi₁; linarith [c.η_pos]

/-- Along a segment in the region of `q` ending with `σ u > 0`, `Q` does not increase. -/
theorem Qq_le_of_segment (hk : k.Good) {x : M} {t : ℝ} (ht : 0 ≤ t)
    (hall : ∀ s ∈ Icc 0 t, k.Φ s x ∈ k.Rq)
    (hpos : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ t x))) :
    c.Qq (c.d.χ.symm (k.Φ t x)) ≤ c.Qq (c.d.χ.symm x) := by
  have hq : ∀ s ∈ Icc 0 t, k.Φ s x ∈ c.qBall' := fun s hs => k.Rq_subset_qBall' hk (hall s hs)
  have hσ := k.σ_uq_pos_of_pos_end hq hpos
  have h := k.antitoneOn_Qq_Φ hq (fun s hs => (hσ s hs).le) (left_mem_Icc.2 ht)
    (right_mem_Icc.2 ht) ht
  simp only at h
  rwa [k.Φ_zero] at h

/-- **Exit from the upper region of `q`**: through the lower face, or through the level `hi₁`
into the middle band (with `Q ≤ Q'`, hence in `Tmid ∩ RqPos`). -/
theorem exists_exit_RqPos_face (hk : k.Good) {x : M} (hx : x ∈ k.RqPos) :
    ∃ t, 0 ≤ t ∧ (∀ s ∈ Icc 0 t, k.Φ s x ∈ k.Rq) ∧
      (c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ t x)) = -(2 * k.δ) ∨
        (f (k.Φ t x) = c.hi₁ ∧ k.Φ t x ∈ k.Tmid ∧ k.Φ t x ∈ k.RqPos ∧
          c.Qq (c.d.χ.symm (k.Φ t x)) ≤ c.Qq (c.d.χ.symm x))) := by
  obtain ⟨t, ht, hall, -, hface⟩ := k.exists_exit_Rq_face hk (k.RqPos_subset_Rq hx)
  refine ⟨t, ht, hall, ?_⟩
  rcases hface with h | h
  · exact Or.inl h
  · right
    have htR := hall t (right_mem_Icc.2 ht)
    have hy := k.symm_mem_RegQ_of_mem_Rq hk htR
    have hq := k.Rq_subset_qBall' hk htR
    have hχ : c.d.χ (c.d.χ.symm (k.Φ t x)) = k.Φ t x :=
      c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
    obtain ⟨huB, hT⟩ := k.hi₁_face hk hy (by rw [hχ]; exact h)
    rw [hχ] at hT
    have hpos : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ t x)) := c.uB_pos.trans_le huB
    have hQ := k.Qq_le_of_segment hk ht hall hpos
    have hxQ := (k.symm_mem_RegQPos_of_mem_RqPos hk hx).2.2.2
    have hQ' : c.Qq (c.d.χ.symm (k.Φ t x)) ≤ k.Q' := hQ.trans hxQ
    have hsq := k.symm_Φ_q_sq_lt hq
    have hζ : ‖c.ζ (k.Φ t x)‖ ≤ k.δ' := by
      have := (c.norm_ζ_le_iff_Qq_le k hsq (by rw [hχ]; exact hT.1)).2 hQ'
      rwa [hχ] at this
    refine ⟨h, ⟨k.mem_Sσ_iff.2 ⟨hT, ⟨?_, ?_⟩, hζ⟩, ?_, h.le⟩,
      k.mem_RqPos_of_symm hq ⟨hpos.le, hy.2.1, hy.2.2, hQ'⟩, hQ⟩
    · rw [h]; linarith [c.lo₂_lt_hi₁, c.lo₂_mem_levels]
    · rw [h]; exact c.hi₁_mem_levels
    · rw [h]; exact c.lo₂_lt_hi₁.le


/-! ### The terminal descent from the lower face -/

/-- **Terminal descent**: from the lower face `σ u = -2δ` of the region of `q`, the trajectory
descends below the level `a'` (along the original field, avoiding `K`: first to the level
`f q - ε` in a left tube around the other arm `z₁`, then by the hypothesis `harm`). -/
theorem exists_f_le_a'_of_face (hk : k.Good) {y : Fin n → ℝ} (hy : y ∈ k.RegQ)
    (hu : c.σ * uq c.d.hk c.hkq y = -(2 * k.δ)) :
    ∃ T, 0 ≤ T ∧ f (k.Φ T (c.d.χ y)) ≤ a' := by
  have hδ := k.hδ
  have hσ2 := c.σ_sq
  have hsq := k.sq_lt_of_mem_RegQ hk hy
  have hyR := c.morseNorm_le_R_of_sq_lt hsq
  have hν := hk.ν_sq_lt_ε
  have hv2 : ‖posPart c.d.hk y‖ ^ 2 ≤ k.ν ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy.2.2 2
  have hu2 : uq c.d.hk c.hkq y ^ 2 = 4 * k.δ ^ 2 := by
    have : (c.σ * uq c.d.hk c.hkq y) ^ 2 = uq c.d.hk c.hkq y ^ 2 := by
      rw [mul_pow]; nlinarith
    rw [← this, hu]; ring
  have hneg2 : ‖negPart c.d.hk y‖ ^ 2 = 4 * k.δ ^ 2 := by
    rw [norm_negPart_sq c.d.hk c.hkq, hu2]
  have hε := c.hε
  have hrm := c.hrmq
  have hδε := k.δ_sq_lt
  set x := c.d.χ y with hxdef
  -- the model exit lemma
  obtain ⟨t₁, ht₁, hft, hstay, -⟩ := exists_exit_mem_leftTube (D := c.D) c.hfs c.hq c.hε (y := y)
    (by nlinarith) (by
      intro h
      have := congrArg (fun z => ‖z‖ ^ 2) h
      simp only [norm_zero] at this
      rw [hneg2] at this; nlinarith)
    (by
      rw [morseNormalForm_split, hneg2]
      nlinarith [sq_nonneg ‖posPart c.d.hk y‖])
    (ρ := hk.ρ₁) (by rw [hneg2]; nlinarith [hk.hδarm, k.ν_sq])
  -- the segment lies in the model ball of `q`
  have hmodel : ∀ s ∈ Icc 0 t₁, c.D.flow s x ∈ c.d.χ '' {z | morseNorm n z < c.D.rm q c.hq} := by
    intro s hs
    refine image_mono (fun z hz => ?_) (hstay s hs)
    show morseNorm n z < c.D.rm q c.hq
    have hz' : morseNorm n z ^ 2 ≤ 2 * c.ε + 2 * ‖posPart c.d.hk y‖ ^ 2 := hz
    exact (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg z) c.rmq_pos.le two_ne_zero).1
      (by nlinarith)
  set γ : ℝ → Fin n → ℝ := fun s => c.d.χ.symm (c.D.flow s x) with hγ
  have hγ' : ∀ s ∈ Icc 0 t₁, HasDerivAt γ (ModelField.modelField c.d.k c.d.r₀ (γ s)) s :=
    hasDerivAt_symm_flow_Icc (D := c.D) c.hq hmodel
  have hγ0 : γ 0 = y := by
    show c.d.χ.symm (c.D.flow 0 x) = y
    rw [c.D.flow_zero, hxdef, c.chart_q_symm_eq' hsq]
  have hχγ : ∀ s ∈ Icc 0 t₁, c.d.χ (γ s) = c.D.flow s x := fun s hs =>
    c.d.symm_image_eq (c.D.modelBall_subset_image_ball q c.hq (hmodel s hs))
  have hγrm : ∀ s ∈ Icc 0 t₁, morseNorm n (γ s) < c.D.rm q c.hq := by
    intro s hs
    obtain ⟨z, hz, hzs⟩ := hmodel s hs
    show morseNorm n (c.d.χ.symm (c.D.flow s x)) < _
    rw [← hzs, c.d.χ.left_inv (c.d.hsrc z (le_of_lt (lt_of_lt_of_le hz (c.D.hrm q c.hq).2)))]
    exact hz
  -- `u²` is monotone along the segment
  have hmono : MonotoneOn (fun s => ‖negPart c.d.hk (γ s)‖ ^ 2) (Icc 0 t₁) :=
    monotoneOn_Icc_of_hasDerivAt_nonneg
      (fun s hs => ModelField.hasDerivAt_normSq_negPart_curve c.d.hk hγ' hs) fun s _ => by
        have := ModelField.theta_pos c.d.hr₀ (γ s); positivity
  have hu_ge : ∀ s ∈ Icc 0 t₁, 4 * k.δ ^ 2 ≤ ‖negPart c.d.hk (γ s)‖ ^ 2 := by
    intro s hs
    have h := hmono (left_mem_Icc.2 (hs.1.trans hs.2)) hs hs.1
    simp only [hγ0, hneg2] at h
    exact h
  have hne : ∀ s ∈ Icc 0 t₁, uq c.d.hk c.hkq (γ s) ≠ 0 := by
    intro s hs h0
    have := hu_ge s hs
    rw [norm_negPart_sq c.d.hk c.hkq, h0] at this
    nlinarith
  -- the sign of `σ u` along the segment
  have hsign : ∀ s ∈ Icc 0 t₁, c.σ * uq c.d.hk c.hkq (γ s) < 0 := by
    intro s hs
    have hstay' : ∀ u ∈ uIcc 0 s, c.D.flow u x ∈ c.qBall := by
      intro u hu
      rw [uIcc_of_le hs.1] at hu
      exact hmodel u ⟨hu.1, hu.2.trans hs.2⟩
    have hne' : ∀ u ∈ uIcc 0 s, uq c.d.hk c.hkq (c.d.χ.symm (c.D.flow u x)) ≠ 0 := by
      intro u hu
      rw [uIcc_of_le hs.1] at hu
      exact hne u ⟨hu.1, hu.2.trans hs.2⟩
    have hprod := c.uq_sign_const hstay' hne'
    have hx0 : c.d.χ.symm x = y := by rw [hxdef, c.chart_q_symm_eq' hsq]
    rw [hx0] at hprod
    have hneg : c.σ * uq c.d.hk c.hkq y < 0 := by rw [hu]; linarith
    have e : (c.σ * uq c.d.hk c.hkq (γ s)) * (c.σ * uq c.d.hk c.hkq y) =
        uq c.d.hk c.hkq (c.d.χ.symm (c.D.flow s x)) * uq c.d.hk c.hkq y := by
      show (c.σ * uq c.d.hk c.hkq (c.d.χ.symm (c.D.flow s x))) * (c.σ * uq c.d.hk c.hkq y) = _
      linear_combination (uq c.d.hk c.hkq (c.d.χ.symm (c.D.flow s x)) * uq c.d.hk c.hkq y) * hσ2
    have hpos : 0 < (c.σ * uq c.d.hk c.hkq (γ s)) * (c.σ * uq c.d.hk c.hkq y) := by
      rw [e]; exact hprod
    exact neg_of_mul_pos_left hpos hneg.le
  have hsign' : ∀ s ∈ Icc 0 t₁, c.σ * uq c.d.hk c.hkq (γ s) ≤ -(2 * k.δ) := by
    intro s hs
    have h1 := hsign s hs
    have h2 := hu_ge s hs
    rw [norm_negPart_sq c.d.hk c.hkq] at h2
    have h3 : (2 * k.δ) ^ 2 ≤ (c.σ * uq c.d.hk c.hkq (γ s)) ^ 2 := by
      rw [mul_pow]; nlinarith
    have h4 : 2 * k.δ ≤ |c.σ * uq c.d.hk c.hkq (γ s)| := by
      rw [← sq_le_sq₀ (by linarith) (abs_nonneg _), sq_abs]; exact h3
    rw [abs_of_neg h1] at h4
    linarith
  -- the endpoint of the segment
  set z' := c.D.flow t₁ x with hz'def
  have hz'γ : c.d.χ (γ t₁) = z' := hχγ t₁ (right_mem_Icc.2 ht₁)
  have hγt₁R : morseNorm n (γ t₁) ≤ c.d.R :=
    (hγrm t₁ (right_mem_Icc.2 ht₁)).le.trans (c.D.hrm q c.hq).2
  have hnf : morseNormalForm c.d.hk (f q) (γ t₁) = f q - c.ε := by
    rw [← c.d.hnorm _ hγt₁R, hz'γ]; exact hft
  have hprod := ModelField.normSq_negPart_mul_posPart_const c.d.hk hγ' t₁ (right_mem_Icc.2 ht₁)
  rw [hγ0, hneg2] at hprod
  have hharm := hk.harm (γ t₁) hnf (hsign t₁ (right_mem_Icc.2 ht₁))
    (by rw [hprod]; nlinarith [hk.hδarm, k.ν_sq])
  rw [hz'γ] at hharm
  obtain ⟨havoid₂, hfT₂⟩ := hharm
  -- `z'` and the whole segment are outside the basin of `p`
  have hz'basin : z' ∉ c.D.basin p c.hp := c.notMem_basin_of_f_lt hfT₂
  have hseg_basin : ∀ s ∈ Icc 0 t₁, c.D.flow s x ∉ c.D.basin p c.hp := by
    intro s hs hmem
    apply hz'basin
    have := (flow_mem_basin_iff (D := c.D) c.hkp (t₁ - s)).2 hmem
    rwa [flow_flow, add_sub_cancel] at this
  -- the segment avoids `K`
  have havoid₁ : ∀ s ∈ Icc 0 t₁, c.D.flow s x ∉ k.K := by
    intro s hs hK
    rcases hK with (hKp | hKq) | hS
    · -- the chart of `p` is disjoint from the chart of `q`
      have h1 : c.D.flow s x ∈ c.d.χ '' Metric.ball 0 c.d.R' :=
        c.D.modelBall_subset_image_ball q c.hq (hmodel s hs)
      have h2 : c.D.flow s x ∈ c.e.χ '' Metric.ball 0 c.e.R' :=
        image_mono k.Kp_subset_ball hKp
      exact (c.D.disjoint p c.hp q c.hq c.p_ne_q).notMem_of_mem_left h2 h1
    · obtain ⟨y', hy', hy'x⟩ := hKq
      have h1 : γ s = y' := by
        show c.d.χ.symm (c.D.flow s x) = y'
        rw [← hy'x, c.d.χ.left_inv (c.d.hball (k.Kq_subset_ball hy'))]
      have := hsign' s hs
      rw [h1] at this
      linarith [hy'.2.2]
    · exact hseg_basin s hs (hk.Sσ_subset_basin hS)
  have hΦ₁ : k.Φ t₁ x = z' :=
    k.Φ_eq_flow_of_avoid (fun s hs => havoid₁ s (Ico_subset_Icc_self hs)) t₁ (right_mem_Icc.2 ht₁)
  have hΦ₂ : k.Φ hk.T₂ z' = c.D.flow hk.T₂ z' :=
    k.Φ_eq_flow_of_avoid (fun s hs => havoid₂ s (Ico_subset_Icc_self hs)) hk.T₂
      (right_mem_Icc.2 hk.hT₂)
  refine ⟨t₁ + hk.T₂, by linarith [hk.hT₂], ?_⟩
  rw [k.Φ_add, hΦ₁, hΦ₂]
  exact hfT₂.le

/-! ### The lower region of `q` -/

/-- **The lower region is forward invariant until the lower face is hit.** -/
theorem Φ_mem_RqNeg_until (hk : k.Good) {x : M} (hx : x ∈ k.RqNeg) {t : ℝ}
    (hF : ∀ s ∈ Icc 0 t, k.Φ s x ∉ k.FqLow) : ∀ s ∈ Icc 0 t, k.Φ s x ∈ k.RqNeg := by
  have hQ : IsClosed {s : ℝ | k.Φ s x ∈ k.RqNeg} :=
    (k.isCompact_RqNeg hk).isClosed.preimage (k.continuous_Φ_curve x)
  refine Icc_subset_of_isClosed_of_step hQ (by simp [hx]) fun s hs hIcc => ?_
  have hsR : k.Φ s x ∈ k.RqNeg := hIcc (right_mem_Icc.2 hs.1)
  have hsq : k.Φ s x ∈ c.qBall' := k.Rq_subset_qBall' hk (k.RqNeg_subset_Rq hsR)
  have hy := k.symm_mem_RegQNeg_of_mem_RqNeg hk hsR
  have hsu : -(2 * k.δ) < c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s x)) := by
    by_contra h
    exact hF s (Ico_subset_Icc_self hs) (k.mem_FqLow_of hsq (not_lt.1 h))
  have hO : k.Φ s x ∈ c.qBall' ∩ {w | -(2 * k.δ) < c.σ * uq c.d.hk c.hkq (c.d.χ.symm w)} :=
    ⟨hsq, hsu⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open
    (c.isOpen_qBall'_inter (P := fun r => -(2 * k.δ) < r)
      (isOpen_lt continuous_const continuous_id)) hO
  refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (s + ε) t, lt_min (by linarith) hs.2,
    fun s' hs' => ?_⟩
  have hs'ε : s' ≤ s + ε := hs'.2.trans (min_le_left _ _)
  have hall : ∀ u ∈ Icc s s', k.Φ u x ∈ c.qBall' := fun u hu =>
    (hεO u ⟨by linarith [hu.1], hu.2.trans hs'ε⟩).1
  obtain ⟨hs'q, hs'u⟩ := hεO s' ⟨by linarith [hs'.1], hs'ε⟩
  refine k.mem_RqNeg_of_symm hs'q ⟨hs'u.le, ?_, ?_⟩
  · exact k.σ_uq_nonpos_Φ hall hy.2.1 s' (right_mem_Icc.2 hs'.1.le)
  · have hanti := k.antitoneOn_normSq_posPart_Φ hall
    have h1 : ‖posPart c.d.hk (c.d.χ.symm (k.Φ s' x))‖ ^ 2 ≤
        ‖posPart c.d.hk (c.d.χ.symm (k.Φ s x))‖ ^ 2 :=
      hanti (left_mem_Icc.2 hs'.1.le) (right_mem_Icc.2 hs'.1.le) hs'.1.le
    have h2 : ‖posPart c.d.hk (c.d.χ.symm (k.Φ s x))‖ ^ 2 ≤ k.ν ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hy.2.2 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.ν_pos.le two_ne_zero).1 (h1.trans h2)

/-- **Exit from the lower region of `q`** (LaSalle pair: `σ u` decreases, `-‖v‖²` increases
where `σ u` is stationary). -/
theorem exists_exit_RqNeg (hk : k.Good) : ∀ x ∈ k.RqNeg, ∃ t, 0 ≤ t ∧ k.Φ t x ∉ k.RqNeg := by
  have hm0 := c.m'_pos
  refine k.exists_exit_of_lyapunov_pair (k.isCompact_RqNeg hk)
    (L₁ := fun y => c.σ * uq c.d.hk c.hkq (c.d.χ.symm y))
    (L₂ := fun y => -‖posPart c.d.hk (c.d.χ.symm y)‖ ^ 2)
    ((continuous_const.mul (continuous_uq c.d.hk c.hkq)).comp_continuousOn
      (c.continuousOn_symm_qBall'.mono ((k.RqNeg_subset_Rq).trans (k.Rq_subset_qBall' hk))))
    ((c.d.continuous_posPart.norm.pow 2).neg.comp_continuousOn
      (c.continuousOn_symm_qBall'.mono ((k.RqNeg_subset_Rq).trans (k.Rq_subset_qBall' hk))))
    (Z := {y | c.σ * uq c.d.hk c.hkq (c.d.χ.symm y) = 0 ∧
      βq c.d.hk c.hkq k.δ k.τ c.σ (c.d.χ.symm y) * ψq c.d.hk c.hkq c.uA c.uB (c.d.χ.symm y) = 0})
    ?_ ?_
  · intro x hx
    have hxq : k.Φ 0 x ∈ c.qBall' := by
      rw [k.Φ_zero]; exact k.Rq_subset_qBall' hk (k.RqNeg_subset_Rq hx)
    have hd := (k.hasDerivAt_uq_Φ hxq).const_mul c.σ
    rw [k.Φ_zero] at hd hxq
    have hy := k.symm_mem_RegQNeg_of_mem_RqNeg hk hx
    have hsq := c.symm_sq_lt_of_mem_qBall' hxq
    set y := c.d.χ.symm x with hydef
    have hC := k.Cq_eq_zero_of_σ_uq_nonpos hsq hy.2.1
    have hB := k.Bq_eq_zero_of_σ_uq_nonpos hsq hy.2.1
    have hσ2 := c.σ_sq
    have hθ := ModelField.theta_pos c.d.hr₀ y
    have hβψ : 0 ≤ βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y :=
      mul_nonneg (βq_nonneg _ _ _) (ψq_nonneg _ _ _)
    have hval : c.σ * uq c.d.hk c.hkq (k.Vq y) = ModelField.theta c.d.r₀ y *
        (c.σ * uq c.d.hk c.hkq y) -
        c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y) := by
      rw [k.uq_Vq hsq, hC, hB]
      linear_combination
        (-(c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y))) * hσ2
    refine ⟨_, ?_, hd, fun h0 => ?_⟩
    · rw [hval]; nlinarith [mul_nonpos_iff.2 (Or.inl ⟨hθ.le, hy.2.1⟩)]
    · rw [hval] at h0
      have h1 : ModelField.theta c.d.r₀ y * (c.σ * uq c.d.hk c.hkq y) ≤ 0 :=
        mul_nonpos_iff.2 (Or.inl ⟨hθ.le, hy.2.1⟩)
      have h2 : 0 ≤ c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y) :=
        mul_nonneg hm0.le hβψ
      have h3 : ModelField.theta c.d.r₀ y * (c.σ * uq c.d.hk c.hkq y) = 0 := by linarith
      have h4 : c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y) = 0 := by
        linarith
      refine ⟨?_, ?_⟩
      · rcases mul_eq_zero.1 h3 with h | h
        · exact absurd h hθ.ne'
        · exact h
      · rcases mul_eq_zero.1 h4 with h | h
        · exact absurd h hm0.ne'
        · exact h
  · rintro x ⟨hx, hu, hβψ⟩
    have hxq : k.Φ 0 x ∈ c.qBall' := by
      rw [k.Φ_zero]; exact k.Rq_subset_qBall' hk (k.RqNeg_subset_Rq hx)
    have hd := (k.hasDerivAt_normSq_posPart_Φ hxq).neg
    rw [k.Φ_zero] at hd hxq
    have hsq := c.symm_sq_lt_of_mem_qBall' hxq
    set y := c.d.χ.symm x with hydef
    have hu0 : uq c.d.hk c.hkq y = 0 := by
      rcases mul_eq_zero.1 hu with h | h
      · exact absurd h c.σ_ne_zero
      · exact h
    have hψ : ψq c.d.hk c.hkq c.uA c.uB y = 1 :=
      ψq_eq_one c.d.hk c.hkq c.uA_pos.le c.uA_lt_uB (by rw [hu0]; nlinarith [sq_nonneg c.uA])
    have hβ : βq c.d.hk c.hkq k.δ k.τ c.σ y = 0 := by
      rw [hψ, mul_one] at hβψ; exact hβψ
    have hv : 2 * k.δ ^ 2 ≤ ‖posPart c.d.hk y‖ ^ 2 := by
      unfold βq at hβ
      rw [hu0] at hβ
      have hS1 : S ((-(c.σ * 0) - k.δ / 2) / (k.δ / 2)) = 1 :=
        S_eq_one (div_nonpos_of_nonpos_of_nonneg (by linarith [k.hδ]) (by linarith [k.hδ]))
      rw [hS1, mul_one, S_eq_zero_iff, le_div_iff₀ (by have := k.hδ; positivity)] at hβ
      nlinarith [sq_nonneg k.τ]
    refine ⟨_, ?_, hd⟩
    have hA := k.Aq_pos hsq
    have hδ := k.hδ
    have hv0 : 0 < ‖posPart c.d.hk y‖ ^ 2 := by nlinarith
    nlinarith [mul_pos hA hv0]

/-- **The lower region of `q` reaches its lower face.** -/
theorem exists_reach_face_of_mem_RqNeg (hk : k.Good) {x : M} (hx : x ∈ k.RqNeg) :
    ∃ t, 0 ≤ t ∧ k.Φ t x ∈ k.RqNeg ∧
      c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ t x)) = -(2 * k.δ) := by
  obtain ⟨t, ht, hexit⟩ := k.exists_exit_RqNeg hk x hx
  obtain ⟨t₁, ht₁, -, ht₁F, hall, -⟩ := k.exists_first_hit_face (k.isCompact_RqNeg hk).isClosed
    k.isClosed_FqLow hx (fun t hF => k.Φ_mem_RqNeg_until hk hx hF) ht hexit
  have ht₁R := hall t₁ (right_mem_Icc.2 ht₁)
  exact ⟨t₁, ht₁, ht₁R, le_antisymm (k.σ_uq_le_of_mem_FqLow ht₁F)
    (k.symm_mem_RegQNeg_of_mem_RqNeg hk ht₁R).1⟩

/-- **Descent from the lower region of `q` below `a'`.** -/
theorem exists_f_le_a'_of_mem_RqNeg (hk : k.Good) {x : M} (hx : x ∈ k.RqNeg) :
    ∃ T, 0 ≤ T ∧ f (k.Φ T x) ≤ a' := by
  obtain ⟨t, ht, htR, htu⟩ := k.exists_reach_face_of_mem_RqNeg hk hx
  have hy := k.RqNeg_subset_Rq htR
  have hq := k.Rq_subset_qBall' hk hy
  obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_face hk (k.symm_mem_RegQ_of_mem_Rq hk hy) htu
  rw [c.d.symm_image_eq (c.qBall'_subset_image_ball hq)] at hfT
  exact ⟨t + T, by linarith, by rw [k.Φ_add]; exact hfT⟩

/-- **Descent from the lower face of the region of `q` below `a'`** (a point of `M`). -/
theorem exists_f_le_a'_of_mem_Rq_face (hk : k.Good) {x : M} (hx : x ∈ k.Rq)
    (hu : c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) = -(2 * k.δ)) :
    ∃ T, 0 ≤ T ∧ f (k.Φ T x) ≤ a' := by
  have hq := k.Rq_subset_qBall' hk hx
  obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_face hk (k.symm_mem_RegQ_of_mem_Rq hk hx) hu
  rw [c.d.symm_image_eq (c.qBall'_subset_image_ball hq)] at hfT
  exact ⟨T, hT, hfT⟩

theorem q_mem_RqNeg : q ∈ k.RqNeg :=
  ⟨0, ⟨by rw [uq_zero, mul_zero]; linarith [k.hδ], by rw [uq_zero, mul_zero],
    by rw [posPart_zero, norm_zero]; exact k.ν_pos.le⟩, c.d.hχ0⟩

/-! ### The axis of `q` -/

theorem AxSet_subset_RegQ : c.AxSet ⊆ k.RegQ := fun y hy =>
  ⟨by linarith [hy.2.1, k.hδ], by rw [hy.1, norm_zero]; nlinarith [hy.2.2],
    by rw [hy.1, norm_zero]; exact k.ν_pos.le⟩

theorem isCompact_Ax (hk : k.Good) : IsCompact c.Ax :=
  c.d.isCompact_image_of_subset
    ((k.isCompact_RegQ hk).of_isClosed_subset c.isClosed_AxSet k.AxSet_subset_RegQ)
    c.sqrt_three_ε_lt_R'q (k.AxSet_subset_RegQ.trans (k.RegQ_subset_le hk))

theorem Ax_subset_Rq : c.Ax ⊆ k.Rq := image_mono k.AxSet_subset_RegQ

theorem symm_mem_AxSet_of_mem_Ax (hk : k.Good) {x : M} (hx : x ∈ c.Ax) :
    c.d.χ.symm x ∈ c.AxSet := by
  obtain ⟨y, hy, rfl⟩ := hx
  rwa [c.chart_q_symm_eq' (k.sq_lt_of_mem_RegQ hk (k.AxSet_subset_RegQ hy))]

/-- The derivative of `σ u` along `Φ` at a point of the axis segment is negative. -/
theorem hasDerivAt_σ_uq_Φ_axis (hk : k.Good) {x : M} {s : ℝ} (hs : k.Φ s x ∈ c.Ax) :
    ∃ r : ℝ, r < 0 ∧ HasDerivAt (fun s => c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s x))) r s := by
  have hq := k.Rq_subset_qBall' hk (k.Ax_subset_Rq hs)
  have hy := k.symm_mem_AxSet_of_mem_Ax hk hs
  have hsq := c.symm_sq_lt_of_mem_qBall' hq
  refine ⟨_, ?_, (k.hasDerivAt_uq_Φ hq).const_mul c.σ⟩
  apply k.σ_uq_Vq_neg_axis hsq hy.1
  rw [c.d.symm_image_eq (c.qBall'_subset_image_ball hq)]
  exact c.lo₂_lt_hi₁.le.trans (k.hi₁_le_f_of_mem_Rq hk (k.Ax_subset_Rq hs))

/-- **The axis segment is forward invariant until `σ u = 0`.** -/
theorem Φ_mem_Ax_until (hk : k.Good) {x : M} (hx : x ∈ c.Ax) {t : ℝ}
    (hF : ∀ s ∈ Icc 0 t, k.Φ s x ∉ c.FqMid) : ∀ s ∈ Icc 0 t, k.Φ s x ∈ c.Ax := by
  have hQ : IsClosed {s : ℝ | k.Φ s x ∈ c.Ax} :=
    (k.isCompact_Ax hk).isClosed.preimage (k.continuous_Φ_curve x)
  refine Icc_subset_of_isClosed_of_step hQ (by simp [hx]) fun s hs hIcc => ?_
  have hsA : k.Φ s x ∈ c.Ax := hIcc (right_mem_Icc.2 hs.1)
  have hsq : k.Φ s x ∈ c.qBall' := k.Rq_subset_qBall' hk (k.Ax_subset_Rq hsA)
  have hy := k.symm_mem_AxSet_of_mem_Ax hk hsA
  have hsu : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s x)) := by
    by_contra h
    exact hF s (Ico_subset_Icc_self hs) (c.mem_FqMid_of hsq (not_lt.1 h))
  have hO : k.Φ s x ∈ c.qBall' ∩ {w | 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm w)} := ⟨hsq, hsu⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open
    (c.isOpen_qBall'_inter (P := fun r => 0 < r) (isOpen_lt continuous_const continuous_id)) hO
  obtain ⟨r, hr, hd⟩ := k.hasDerivAt_σ_uq_Φ_axis hk hsA
  have hev := eventually_lt_of_hasDerivAt_neg hr hd
  obtain ⟨ε₂, hε₂, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  have hε₂' : s < ε₂ := hε₂
  refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (min (s + ε) ε₂) t,
    lt_min (lt_min (by linarith) hε₂') hs.2, fun s' hs' => ?_⟩
  have hs'ε : s' ≤ s + ε := hs'.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs'ε₂ : s' ≤ ε₂ := hs'.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hall : ∀ u ∈ Icc s s', k.Φ u x ∈ c.qBall' := fun u hu =>
    (hεO u ⟨by linarith [hu.1], hu.2.trans hs'ε⟩).1
  obtain ⟨hs'q, hs'u⟩ := hεO s' ⟨by linarith [hs'.1], hs'ε⟩
  have hs'u' : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s' x)) := hs'u
  have hlt := hsub ⟨hs'.1, hs'ε₂⟩
  have hσ2 := c.σ_sq
  refine c.mem_Ax_of_symm hs'q ⟨?_, hs'u'.le, ?_⟩
  · have hanti := k.antitoneOn_normSq_posPart_Φ hall
    have h1 : ‖posPart c.d.hk (c.d.χ.symm (k.Φ s' x))‖ ^ 2 ≤
        ‖posPart c.d.hk (c.d.χ.symm (k.Φ s x))‖ ^ 2 :=
      hanti (left_mem_Icc.2 hs'.1.le) (right_mem_Icc.2 hs'.1.le) hs'.1.le
    rw [hy.1, norm_zero] at h1
    have h2 : ‖posPart c.d.hk (c.d.χ.symm (k.Φ s' x))‖ ^ 2 = 0 :=
      le_antisymm (by simpa using h1) (by positivity)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  · have h1 : uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s' x)) ^ 2 =
        (c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s' x))) ^ 2 := by rw [mul_pow]; nlinarith
    have h2 : uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s x)) ^ 2 =
        (c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s x))) ^ 2 := by rw [mul_pow]; nlinarith
    have h3 := hy.2.2
    rw [h2] at h3
    have hlt' : c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s' x)) <
        c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s x)) := hlt
    have h4 : (c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s' x))) ^ 2 ≤
        (c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ s x))) ^ 2 :=
      pow_le_pow_left₀ hs'u'.le hlt'.le 2
    rw [h1]
    linarith

/-- **The axis segment reaches `q`.** -/
theorem exists_reach_q_of_mem_Ax (hk : k.Good) {x : M} (hx : x ∈ c.Ax) :
    ∃ t, 0 ≤ t ∧ k.Φ t x = q := by
  -- exit from the compact axis segment (LaSalle with `-σ u`)
  obtain ⟨t, ht, hexit⟩ := k.exists_exit_of_deriv_pos (k.isCompact_Ax hk)
    (L := fun y => -(c.σ * uq c.d.hk c.hkq (c.d.χ.symm y)))
    ((continuous_const.mul (continuous_uq c.d.hk c.hkq)).neg.comp_continuousOn
      (c.continuousOn_symm_qBall'.mono (k.Ax_subset_Rq.trans (k.Rq_subset_qBall' hk))))
    (fun z hz => by
      have hz0 : k.Φ 0 z ∈ c.Ax := by rw [k.Φ_zero]; exact hz
      obtain ⟨r, hr, hd⟩ := k.hasDerivAt_σ_uq_Φ_axis hk hz0
      exact ⟨-r, by linarith, hd.neg⟩) x hx
  obtain ⟨t₁, ht₁, -, ht₁F, hall, -⟩ := k.exists_first_hit_face (k.isCompact_Ax hk).isClosed
    c.isClosed_FqMid hx (fun t hF => k.Φ_mem_Ax_until hk hx hF) ht hexit
  have ht₁A := hall t₁ (right_mem_Icc.2 ht₁)
  have hy := k.symm_mem_AxSet_of_mem_Ax hk ht₁A
  have hq := k.Rq_subset_qBall' hk (k.Ax_subset_Rq ht₁A)
  have hu : c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ t₁ x)) = 0 :=
    le_antisymm (c.σ_uq_le_of_mem_FqMid ht₁F) hy.2.1
  have hu0 : uq c.d.hk c.hkq (c.d.χ.symm (k.Φ t₁ x)) = 0 := by
    rcases mul_eq_zero.1 hu with h | h
    · exact absurd h c.σ_ne_zero
    · exact h
  have hy0 : c.d.χ.symm (k.Φ t₁ x) = 0 := eq_zero_of_uq_eq_zero c.d.hk c.hkq hu0 hy.1
  refine ⟨t₁, ht₁, ?_⟩
  rw [← c.d.symm_image_eq (c.qBall'_subset_image_ball hq), hy0, c.d.hχ0]

/-- **Descent from the axis segment below `a'`.** -/
theorem exists_f_le_a'_of_mem_Ax (hk : k.Good) {x : M} (hx : x ∈ c.Ax) :
    ∃ T, 0 ≤ T ∧ f (k.Φ T x) ≤ a' := by
  obtain ⟨t, ht, hq⟩ := k.exists_reach_q_of_mem_Ax hk hx
  obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_RqNeg hk k.q_mem_RqNeg
  exact ⟨t + T, by linarith, by rw [k.Φ_add, hq]; exact hfT⟩

/-- A point of the upper region on the axis lies in the axis segment. -/
theorem mem_Ax_of_mem_RqPos (hk : k.Good) {x : M} (hx : x ∈ k.RqPos)
    (hv : posPart c.d.hk (c.d.χ.symm x) = 0) : x ∈ c.Ax := by
  have hy := k.symm_mem_RegQPos_of_mem_RqPos hk hx
  refine c.mem_Ax_of_symm (k.Rq_subset_qBall' hk (k.RqPos_subset_Rq hx)) ⟨hv, hy.1, ?_⟩
  have := hy.2.1
  rwa [hv, norm_zero, zero_pow two_ne_zero, add_zero] at this

/-- A point of the upper region with `σ u = 0` lies in the lower region. -/
theorem mem_RqNeg_of_mem_RqPos (hk : k.Good) {x : M} (hx : x ∈ k.RqPos)
    (hu : c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) = 0) : x ∈ k.RqNeg := by
  have hy := k.symm_mem_RegQPos_of_mem_RqPos hk hx
  exact k.mem_RqNeg_of_symm (k.Rq_subset_qBall' hk (k.RqPos_subset_Rq hx))
    ⟨by rw [hu]; linarith [k.hδ], hu.le, hy.2.2.1⟩

/-! ### The support set of the tube piece above `hi₁`, and the classification of `K` -/

/-- **The support set of the tube piece above the level `hi₁` lies in the upper region of
`q`.** -/
theorem Sσ_high_subset_RqPos (hk : k.Good) : k.Sσ ∩ {x | c.hi₁ ≤ f x} ⊆ k.RqPos := by
  rintro x ⟨hx, hf⟩
  have hf' : c.hi₁ ≤ f x := hf
  obtain ⟨hT, hfI, hζ⟩ := k.mem_Sσ_iff.1 hx
  -- the level point `w x` and the time to `x`
  obtain ⟨y, hy, hyπ⟩ := hx.2
  have hyrm := k.morseNorm_lt_rm_of_mem_Sq hy
  have hw : c.w x = y := by
    unfold w
    rw [← hyπ, c.d.χ.left_inv (c.d.hsrc y (hyrm.le.trans (c.D.hrm q c.hq).2))]
  have hxflow : c.D.flow (c.c₂ - f x) (c.d.χ y) = x := by rw [hyπ]; exact c.flow_π_eq
  have hy1 : morseNorm n y ^ 2 ≤ 2 * k.δ' ^ 2 + 2 * c.ε₂ := hy.1
  have hε := c.hε
  have hrm := c.hrmq
  have hη := c.η_lt_ε
  have hε₂ := c.ε₂_lt_ε
  have h8 := hk.hδ'8
  have hbound : 2 * k.δ' ^ 2 + 2 * c.ε₂ + c.η < 3 * c.ε := by
    have := c.η_pos
    have h1 : c.η < c.ε / 4 := by
      have := c.η_lt_right
      have h2 : c.ε₂ - c.d.r₀ ^ 2 / 2 = c.ε / 2 - c.d.r₀ ^ 2 / 4 := by unfold ε₂; ring
      have h3 : c.η ≤ (c.ε₂ - c.d.r₀ ^ 2 / 2) / 2 := by
        unfold η; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      have hr0 : 0 < c.d.r₀ ^ 2 := by have := c.d.hr₀; positivity
      linarith
    linarith
  -- `x` is in the chart ball `qBall'`
  have hxq : ∃ z : Fin n → ℝ, morseNorm n z ^ 2 < 3 * c.ε ∧ c.d.χ z = x := by
    have hfhi : c.hi₁ ≤ f x := hf'
    have hflev := hfI.2
    rcases le_or_gt 0 (c.c₂ - f x) with ht | ht
    · have hmem := c.flow_mem_qBall_of_nonneg hyrm ht (t := c.c₂ - f x)
        (by unfold hi₁ at hfhi; nlinarith) (c.c₂ - f x) (right_mem_Icc.2 ht)
      rw [hxflow] at hmem
      obtain ⟨z, hz, hzx⟩ := hmem
      refine ⟨z, ?_, hzx⟩
      have hz' : morseNorm n z ^ 2 ≤ morseNorm n y ^ 2 + 2 * (c.c₂ - f x) := hz
      unfold hi₁ at hfhi; nlinarith
    · have hmem := c.flow_mem_qBall_of_nonpos hyrm ht.le (t := c.c₂ - f x)
        (by nlinarith) (c.c₂ - f x) (left_mem_Icc.2 ht.le)
      rw [hxflow] at hmem
      obtain ⟨z, hz, hzx⟩ := hmem
      refine ⟨z, ?_, hzx⟩
      have hz' : morseNorm n z ^ 2 ≤ morseNorm n y ^ 2 - 2 * (c.c₂ - f x) := hz
      nlinarith
  obtain ⟨z, hz, rfl⟩ := hxq
  have hzR := c.morseNorm_le_R_of_sq_lt hz
  have hσu := c.σ_uq_pos_of_mem_TubeOpenσ hz hT
  have hQ := (c.norm_ζ_le_iff_Qq_le k hz hT.1).1 hζ
  refine ⟨z, ⟨hσu.le, (c.hi₁_le_iff hzR).1 hf', ?_, hQ⟩, rfl⟩
  -- the bound on `‖v‖` from `Q ≤ Q'` and `u² ≥ 2ε₂ - η`
  have hfz := c.f_chart_q hzR
  have hu2 : 2 * c.ε₂ - c.η ≤ uq c.d.hk c.hkq z ^ 2 := by
    have := hfI.2; unfold c₂ at this
    nlinarith [sq_nonneg ‖posPart c.d.hk z‖]
  have hQz := c.Qq_eq_uq z
  have hpos := c.two_ε₂_sub_η_pos
  have hν := k.νm_sq
  have hνm := k.νm_le_ν
  have hv2 : ‖posPart c.d.hk z‖ ^ 2 ≤ k.νm ^ 2 := by
    rw [hν, le_div_iff₀ hpos]
    nlinarith [sq_nonneg ‖posPart c.d.hk z‖]
  have hv3 : ‖posPart c.d.hk z‖ ^ 2 ≤ k.ν ^ 2 := hv2.trans (pow_le_pow_left₀ k.νm_nonneg hνm 2)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.ν_pos.le two_ne_zero).1 hv3

/-- **Classification of the points of `K`**: in the ball region of `p`, in the middle band, or
in the region of `q`. -/
theorem mem_K_cases (hk : k.Good) {x : M} (hx : x ∈ k.K) :
    x ∈ c.Wball ∨ x ∈ k.Tmid ∨ x ∈ k.Rq := by
  rcases hx with (hKp | hKq) | hS
  · left
    obtain ⟨y, hy, rfl⟩ := hKp
    exact ⟨y, morseNorm_le_of_mem_Kp hy, rfl⟩
  · right; right
    obtain ⟨y, hy, rfl⟩ := hKq
    refine ⟨y, ⟨by linarith [hy.2.2, k.hδ], by nlinarith [hy.1, sq_nonneg ‖posPart c.d.hk y‖],
      ?_⟩, rfl⟩
    have h1 := hy.2.1
    have h2 := hy.1
    have hτ : 0 ≤ k.τ ^ 2 := sq_nonneg _
    have h3 : ‖posPart c.d.hk y‖ ^ 2 ≤ k.ν ^ 2 := by
      rw [k.ν_sq]; nlinarith [sq_nonneg k.νm]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.ν_pos.le two_ne_zero).1 h3
  · rcases le_or_gt (f x) c.lo₂ with h1 | h1
    · exact Or.inl (hk.Sσ_low_subset_Wball ⟨hS, h1⟩)
    · rcases le_or_gt (f x) c.hi₁ with h2 | h2
      · exact Or.inr (Or.inl ⟨hS, h1.le, h2⟩)
      · exact Or.inr (Or.inr (k.RqPos_subset_Rq (k.Sσ_high_subset_RqPos hk ⟨hS, h2.le⟩)))

end CancelConsts

end CancelData

end GradientLikeStrip

end

end PoincareHighDim
