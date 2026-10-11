/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Morse.Cancellation.Flow.CancelFlowQ2

/-!
# Cancellation, step C4c: the forward completion (`reaches_bottom`)

Phase B, step C4c (`CancelFlowExit`). For the cancellation data `c : CancelData I f a' b' p q`,
transverse constants `k : c.CancelConsts` and the additional smallness hypotheses
`hk : k.Good` (module `CancelGood`), this module proves

```
theorem reaches_bottom (hk : k.Good) {x : M} (hx : f x ∈ Icc a' b') :
    ∃ t, 0 ≤ t ∧ f (k.Φ t x) = a' ∧ ∀ s ∈ Ico 0 t, a' < f (k.Φ s x)
```
(the first-hitting form used by C5), from `exists_f_Φ_le_a'`.

**The cycle exclusion.** The obstruction of C4a — trajectories descending from the middle band
back into the ball of `p` and being pushed up again — is excluded with the **global transported
angle** `L` (`CancelData.L`): the angle `Bm` in the ball of `p`, the transported angle
`Lq = Lσ ∘ ζhat` of the chart point in the ball of `q` (`CancelFlowQ`), and the transported angle
`Lσ ∘ ζ` of the transverse coordinate on the rest of the tube, glued by `Lσ_eq_Bm`
(`CancelGood`) and `ζ_eq_ζhat` (`CancelFlowQ`). On the compact **cycle region**
`Ccyc = Ann ∪ Tmid ∪ RqPos` (annulus of `p`, middle band, upper region of `q`):

* `L` is continuous (`continuousOn_L_Ccyc`) and non-increasing along every trajectory segment
  in `Ccyc` (`antitoneOn_L_Φ`, from right-local decrease in each piece and the local-to-global
  lemma `antitoneOn_Icc_of_right_local`);
* off the strictness set `Zc`, `L` strictly decreases at some later time
  (`exists_L_lt_of_notMem_Zc`: the estimate `hdB` in the annulus, `βm' > 0` in the band, the
  negative rate of the conserved product in the region of `q`);
* every point of `Ccyc` eventually leaves `Ccyc ∩ Zc` (`leaves_of_mem_Ccyc`, by the explicit
  exits of `CancelFlowP` / `CancelFlowQ2`);

so the antitone LaSalle principle (`exists_exit_of_antitone_weak`, `CancelFlowTools`) gives
`exists_exit_Ccyc`. The region is forward invariant until one of its two faces is hit
(`Φ_mem_Ccyc_until`): the inner sphere of the annulus or the stable disc `σ u = 0` of `q`
(`exists_hit_Fc`).

**The assembly** (`exists_f_Φ_le_a'`): off `K` the level strictly decreases
(`exists_hit_K_or_bottom`); a point of `K` is in `Wball`, `Tmid` or `Rq` (`mem_K_cases`);
`Wball` feeds `Wp2 ∩ Tmid` at the level `lo₂` where `L ≤ b₀`, so the first face hit is the
stable disc of `q` (the inner sphere is excluded since `L ≤ b₀` there makes the radius increase,
`exists_f_le_a'_of_mem_Wp2_Tmid`), and the stable disc descends below `a'` through the lower
region of `q` and the terminal descent of the other arm (`CancelFlowQ2`); the region of `q`
exits through its lower face or through the level `hi₁`, into the band or (with a large
transverse coordinate, off `K`) along the original field back into `Wball` or `Tmid`
(`exists_f_le_a'_of_mem_Rq`).

The hypotheses on the constants are exactly the fields of `CancelConsts.Good` (as allowed by the
plan); they are produced by `exists_good` (module `CancelGoodExists`).

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

/-! ### The annulus of `p` -/

/-- The closed annulus `ρs ≤ ‖y‖ ≤ ρB` in the chart of `p`. -/
def Ann : Set M := c.e.χ '' {y | c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB}

theorem isCompact_Ann : IsCompact c.Ann :=
  (c.e.isCompact_image_le c.ρB_lt_R').of_isClosed_subset
    (c.e.isCompact_image_of_subset
      ((isCompact_morseNorm_le c.ρB).of_isClosed_subset
        ((isClosed_le continuous_const continuous_morseNorm).inter
          (isClosed_le continuous_morseNorm continuous_const)) fun _ hy => hy.2)
      c.ρB_lt_R' fun _ hy => hy.2).isClosed (image_mono fun _ hy => hy.2)

theorem Ann_subset_Wball : c.Ann ⊆ c.Wball := image_mono fun _ hy => hy.2

theorem Ann_subset_pBall' : c.Ann ⊆ c.pBall' := c.Ann_subset_Wball.trans c.Wball_subset_pBall'

theorem symm_mem_of_mem_Ann {x : M} (hx : x ∈ c.Ann) :
    c.ρs ≤ morseNorm n (c.e.χ.symm x) ∧ morseNorm n (c.e.χ.symm x) ≤ c.ρB := by
  obtain ⟨y, hy, rfl⟩ := hx
  rwa [c.chart_p_symm_eq' (c.sq_lt_three_ε_of_le_ρB hy.2)]

theorem mem_Ann_of_symm {x : M} (hx : x ∈ c.pBall')
    (h : c.ρs ≤ morseNorm n (c.e.χ.symm x) ∧ morseNorm n (c.e.χ.symm x) ≤ c.ρB) : x ∈ c.Ann :=
  c.e.mem_image_of_symm_mem (c.pBall'_subset_image_ball hx) h

theorem symm_sq_lt_of_mem_pBall' {x : M} (hx : x ∈ c.pBall') :
    morseNorm n (c.e.χ.symm x) ^ 2 < 3 * c.ε := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.chart_p_symm_eq' hy]; exact hy

theorem symm_ne_zero_of_mem_Ann {x : M} (hx : x ∈ c.Ann) : c.e.χ.symm x ≠ 0 := by
  intro h
  have := (c.symm_mem_of_mem_Ann hx).1
  rw [h, morseNorm_zero] at this
  linarith [c.ρs_pos]

theorem f_eq_of_mem_pBall' {x : M} (hx : x ∈ c.pBall') :
    f x = f p + morseNorm n (c.e.χ.symm x) ^ 2 / 2 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.chart_p_symm_eq' hy]
  exact c.f_chart_p ((c.morseNorm_lt_rmp_of_sq_lt hy).le.trans (c.D.hrm p c.hp).2)

theorem f_le_lo₂_of_mem_Ann {x : M} (hx : x ∈ c.Ann) : f x ≤ c.lo₂ := by
  rw [c.f_eq_of_mem_pBall' (c.Ann_subset_pBall' hx)]
  have h := (c.symm_mem_of_mem_Ann hx).2
  have h2 := c.ρB_sq_eq
  have := pow_le_pow_left₀ (ModelField.morseNorm_nonneg _) h 2
  linarith

theorem a'_lt_f_of_mem_pBall' {x : M} (hx : x ∈ c.pBall') : a' < f x := by
  rw [c.f_eq_of_mem_pBall' hx]
  have := c.f_p_mem.1
  nlinarith [sq_nonneg (morseNorm n (c.e.χ.symm x))]

theorem a'_lt_lo₂ : a' < c.lo₂ := by
  have := c.a'_lt_c₁_sub_η; have := c.η_pos; unfold lo₂; linarith

/-- The points of `Tmid` at the level `lo₂` lie in the annulus. -/
theorem mem_Ann_of_mem_Tmid_lo₂ (k : c.CancelConsts) (hk : k.Good) {x : M} (hx : x ∈ k.Tmid)
    (hf : f x = c.lo₂) : x ∈ c.Ann := by
  obtain ⟨hp, hρ⟩ := hk.Sσ_lo₂_radius hx.1 hf
  exact c.mem_Ann_of_symm hp ⟨by rw [hρ]; exact c.ρs_lt_ρB.le, hρ.le⟩

/-- The points of `Tmid` at the level `hi₁` lie in the upper region of `q`. -/
theorem mem_RqPos_of_mem_Tmid_hi₁ (k : c.CancelConsts) (hk : k.Good) {x : M} (hx : x ∈ k.Tmid)
    (hf : f x = c.hi₁) : x ∈ k.RqPos :=
  k.Sσ_high_subset_RqPos hk ⟨hx.1, hf.ge⟩

theorem notMem_pBall'_of_mem_qBall' {x : M} (hx : x ∈ c.qBall') : x ∉ c.pBall' :=
  fun h => c.disjoint_pBall'_qBall'.notMem_of_mem_left h hx

theorem notMem_qBall'_of_mem_pBall' {x : M} (hx : x ∈ c.pBall') : x ∉ c.qBall' :=
  fun h => c.disjoint_pBall'_qBall'.notMem_of_mem_left hx h

open scoped Classical in
/-- **The global transported angle**: the angle `Bm` in the ball of `p`, the transported angle
`Lq` of the chart point in the ball of `q`, the transported angle of the transverse coordinate on
the rest of the one-sided tube, `0` elsewhere. -/
def L (x : M) : ℝ :=
  if x ∈ c.pBall' then Bm c.e₁ (c.e.χ.symm x)
  else if x ∈ c.qBall' then c.Lq (c.d.χ.symm x)
  else if x ∈ c.TubeOpenσ then c.Lσ (c.ζ x) else 0

theorem L_of_mem_pBall' {x : M} (hx : x ∈ c.pBall') : c.L x = Bm c.e₁ (c.e.χ.symm x) := by
  classical simp [L, hx]

theorem L_of_mem_qBall' {x : M} (hx : x ∈ c.qBall') : c.L x = c.Lq (c.d.χ.symm x) := by
  classical simp [L, hx, c.notMem_pBall'_of_mem_qBall' hx]

theorem L_of_mem_tube {x : M} (hp : x ∉ c.pBall') (hq : x ∉ c.qBall') (hT : x ∈ c.TubeOpenσ) :
    c.L x = c.Lσ (c.ζ x) := by
  classical simp [L, hp, hq, hT]

theorem L_nonneg (x : M) : 0 ≤ c.L x := by
  classical
  unfold L
  split_ifs
  · exact Bm_nonneg c.morseNorm_e₁ _
  · exact c.Lq_nonneg _
  · exact c.Lσ_nonneg _
  · exact le_rfl

/-- The continuity of `Bm ∘ χ_p.symm` at a point of the ball of `p` off `p`. -/
theorem continuousAt_Bm_symm {x : M} (hx : x ∈ c.pBall') (h0 : c.e.χ.symm x ≠ 0) :
    ContinuousAt (fun w => Bm c.e₁ (c.e.χ.symm w)) x :=
  (contDiffAt_Bm c.e₁ h0).continuousAt.comp
    (c.e.contMDiffAt_symm (c.pBall'_subset_image_ball hx)).continuousAt

namespace CancelConsts

variable {c} (k : c.CancelConsts)

/-! ### The cycle region and the transported angle -/

/-- The cycle region: the annulus of `p`, the middle band and the upper region of `q`. -/
def Ccyc : Set M := c.Ann ∪ k.Tmid ∪ k.RqPos

theorem isCompact_Ccyc (hk : k.Good) : IsCompact k.Ccyc :=
  (c.isCompact_Ann.union k.isCompact_Tmid).union (k.isCompact_RqPos hk)

theorem Ann_subset_Ccyc : c.Ann ⊆ k.Ccyc := fun _ hx => Or.inl (Or.inl hx)

theorem Tmid_subset_Ccyc : k.Tmid ⊆ k.Ccyc := fun _ hx => Or.inl (Or.inr hx)

theorem RqPos_subset_Ccyc : k.RqPos ⊆ k.Ccyc := fun _ hx => Or.inr hx

theorem a'_lt_f_of_mem_Ccyc (hk : k.Good) {x : M} (hx : x ∈ k.Ccyc) : a' < f x := by
  rcases hx with (h | h) | h
  · exact c.a'_lt_f_of_mem_pBall' (c.Ann_subset_pBall' h)
  · exact c.a'_lt_lo₂.trans_le h.2.1
  · exact c.a'_lt_lo₂.trans (c.lo₂_lt_hi₁.trans_le (k.hi₁_le_f_of_mem_Rq hk (k.RqPos_subset_Rq h)))

theorem notMem_Ccyc_of_f_le (hk : k.Good) {x : M} (hx : f x ≤ a') : x ∉ k.Ccyc :=
  fun h => absurd (k.a'_lt_f_of_mem_Ccyc hk h) (not_lt.2 hx)

/-- A point of the cycle region at a level strictly between `lo₂` and `hi₁` is in `Tmid`. -/
theorem mem_Tmid_of_mem_Ccyc (hk : k.Good) {x : M} (hx : x ∈ k.Ccyc) (h1 : c.lo₂ < f x)
    (h2 : f x < c.hi₁) : x ∈ k.Tmid := by
  rcases hx with (h | h) | h
  · exact absurd (c.f_le_lo₂_of_mem_Ann h) (not_le.2 h1)
  · exact h
  · exact absurd (k.hi₁_le_f_of_mem_Rq hk (k.RqPos_subset_Rq h)) (not_le.2 h2)

theorem f_ge_lo₂_of_mem_RqPos (hk : k.Good) {x : M} (hx : x ∈ k.RqPos) : c.lo₂ ≤ f x :=
  c.lo₂_lt_hi₁.le.trans (k.hi₁_le_f_of_mem_Rq hk (k.RqPos_subset_Rq hx))

theorem RqPos_subset_qBall' (hk : k.Good) : k.RqPos ⊆ c.qBall' :=
  k.RqPos_subset_Rq.trans (k.Rq_subset_qBall' hk)

/-- On the middle band, `L` is the transported angle of the transverse coordinate. -/
theorem L_eq_Lσ_ζ_of_mem_Tmid (hk : k.Good) {x : M} (hx : x ∈ k.Tmid) :
    c.L x = c.Lσ (c.ζ x) := by
  have hT := k.Tmid_subset_TubeOpenσ hx
  have hζ : ‖c.ζ x‖ < hk.δ'' := (k.norm_ζ_le_of_mem_Sσ hx.1).trans_lt hk.hδ'δ''
  by_cases hp : x ∈ c.pBall'
  · rw [c.L_of_mem_pBall' hp, hk.Lσ_eq_Bm hp hT hζ]
  by_cases hq : x ∈ c.qBall'
  · rw [c.L_of_mem_qBall' hq]
    have hχ : c.d.χ (c.d.χ.symm x) = x := c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
    have := Lq_eq_Lσ_ζ (c := c) (c.symm_sq_lt_of_mem_qBall' hq) (by rw [hχ]; exact hT.1)
    rwa [hχ] at this
  · exact c.L_of_mem_tube hp hq hT

/-- The chart point of `p` of a point of the cycle region in the ball of `p` is nonzero. -/
theorem symm_ne_zero_of_mem_Ccyc (hk : k.Good) {x : M} (hx : x ∈ k.Ccyc) (hp : x ∈ c.pBall') :
    c.e.χ.symm x ≠ 0 := by
  rcases hx with (h | h) | h
  · exact c.symm_ne_zero_of_mem_Ann h
  · have hT := k.Tmid_subset_TubeOpenσ h
    have hχ : c.e.χ (c.e.χ.symm x) = x := c.e.symm_image_eq (c.pBall'_subset_image_ball hp)
    exact c.ne_zero_of_mem_TubeOpen (c.symm_sq_lt_of_mem_pBall' hp) (by rw [hχ]; exact hT.1)
  · exact absurd hp (c.notMem_pBall'_of_mem_qBall' (k.RqPos_subset_qBall' hk h))

/-- A point of the cycle region in the ball of `q` has `Q ≤ Q'`. -/
theorem Qq_le_of_mem_Ccyc (hk : k.Good) {x : M} (hx : x ∈ k.Ccyc) (hq : x ∈ c.qBall') :
    c.Qq (c.d.χ.symm x) ≤ k.Q' := by
  rcases hx with (h | h) | h
  · exact absurd hq (c.notMem_qBall'_of_mem_pBall' (c.Ann_subset_pBall' h))
  · have hT := k.Tmid_subset_TubeOpenσ h
    have hχ : c.d.χ (c.d.χ.symm x) = x := c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
    have := (c.norm_ζ_le_iff_Qq_le k (c.symm_sq_lt_of_mem_qBall' hq) (by rw [hχ]; exact hT.1)).1
      (by rw [hχ]; exact k.norm_ζ_le_of_mem_Sσ h.1)
    exact this
  · exact (k.symm_mem_RegQPos_of_mem_RqPos hk h).2.2.2

/-- A point of the cycle region in the ball of `q` has `σ u ≥ 0`. -/
theorem σ_uq_nonneg_of_mem_Ccyc (hk : k.Good) {x : M} (hx : x ∈ k.Ccyc) (hq : x ∈ c.qBall') :
    0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) := by
  rcases hx with (h | h) | h
  · exact absurd hq (c.notMem_qBall'_of_mem_pBall' (c.Ann_subset_pBall' h))
  · have hT := k.Tmid_subset_TubeOpenσ h
    have hχ : c.d.χ (c.d.χ.symm x) = x := c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
    exact (c.σ_uq_pos_of_mem_TubeOpenσ (c.symm_sq_lt_of_mem_qBall' hq) (by rw [hχ]; exact hT)).le
  · exact (k.symm_mem_RegQPos_of_mem_RqPos hk h).1

/-- A point of the middle band in the ball of `q` has `σ u > 0`. -/
theorem σ_uq_pos_of_mem_Tmid {x : M} (hx : x ∈ k.Tmid) (hq : x ∈ c.qBall') :
    0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) := by
  have hT := k.Tmid_subset_TubeOpenσ hx
  have hχ : c.d.χ (c.d.χ.symm x) = x := c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
  exact c.σ_uq_pos_of_mem_TubeOpenσ (c.symm_sq_lt_of_mem_qBall' hq) (by rw [hχ]; exact hT)

/-- The continuity of `Lq ∘ χ_q.symm` at a point of the ball of `q` with `Q ≤ Q'`. -/
theorem continuousAt_Lq_symm (hk : k.Good) {x : M} (hx : x ∈ c.qBall')
    (hQ : c.Qq (c.d.χ.symm x) ≤ k.Q') : ContinuousAt (fun w => c.Lq (c.d.χ.symm w)) x := by
  have h1 : ContinuousAt c.Lq (c.d.χ.symm x) :=
    (hk.continuousAt_Lσ (k.norm_ζhat_lt_δ''_of_Qq_le hk hQ)).comp (c.continuousAt_ζhat _)
  exact h1.comp (c.d.contMDiffAt_symm (c.qBall'_subset_image_ball hx)).continuousAt

/-- **`L` is continuous on the cycle region.** -/
theorem continuousOn_L_Ccyc (hk : k.Good) : ContinuousOn c.L k.Ccyc := by
  intro z hz
  by_cases hp : z ∈ c.pBall'
  · have hev : (fun w => Bm c.e₁ (c.e.χ.symm w)) =ᶠ[𝓝 z] c.L := by
      filter_upwards [c.isOpen_pBall'.mem_nhds hp] with w hw
      exact (c.L_of_mem_pBall' hw).symm
    exact ((c.continuousAt_Bm_symm hp (k.symm_ne_zero_of_mem_Ccyc hk hz hp)).congr
      hev).continuousWithinAt
  by_cases hq : z ∈ c.qBall'
  · have hev : (fun w => c.Lq (c.d.χ.symm w)) =ᶠ[𝓝 z] c.L := by
      filter_upwards [c.isOpen_qBall'.mem_nhds hq] with w hw
      exact (c.L_of_mem_qBall' hw).symm
    exact ((k.continuousAt_Lq_symm hk hq (k.Qq_le_of_mem_Ccyc hk hz hq)).congr
      hev).continuousWithinAt
  -- off both balls: `z ∈ Tmid` with `lo₂ < f z < hi₁`
  have hzT : z ∈ k.Tmid := by
    rcases hz with (h | h) | h
    · exact absurd (c.Ann_subset_pBall' h) hp
    · exact h
    · exact absurd (k.RqPos_subset_qBall' hk h) hq
  have hlo : c.lo₂ < f z := by
    rcases hzT.2.1.eq_or_lt with h | h
    · exact absurd (c.Ann_subset_pBall' (c.mem_Ann_of_mem_Tmid_lo₂ k hk hzT h.symm)) hp
    · exact h
  have hhi : f z < c.hi₁ := by
    rcases hzT.2.2.eq_or_lt with h | h
    · exact absurd (k.RqPos_subset_qBall' hk (c.mem_RqPos_of_mem_Tmid_hi₁ k hk hzT h)) hq
    · exact h
  have hT := k.Tmid_subset_TubeOpenσ hzT
  have hcont : ContinuousAt (fun w => c.Lσ (c.ζ w)) z :=
    (hk.continuousAt_Lσ ((k.norm_ζ_le_of_mem_Sσ hzT.1).trans_lt hk.hδ'δ'')).comp
      (c.continuousOn_ζ.continuousAt (c.isOpen_TubeOpen.mem_nhds hT.1))
  refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ (k.L_eq_Lσ_ζ_of_mem_Tmid hk hzT)
  have hO : {w | c.lo₂ < f w ∧ f w < c.hi₁} ∈ 𝓝 z :=
    ((isOpen_lt continuous_const c.hfs.continuous).inter
      (isOpen_lt c.hfs.continuous continuous_const)).mem_nhds ⟨hlo, hhi⟩
  filter_upwards [nhdsWithin_le_nhds hO, self_mem_nhdsWithin] with w hw hwC
  exact k.L_eq_Lσ_ζ_of_mem_Tmid hk (k.mem_Tmid_of_mem_Ccyc hk hwC hw.1 hw.2)


/-! ### Monotonicity of `L` along trajectories in the cycle region -/

/-- The ball of `p` minus `p` is open. -/
theorem isOpen_pBall'_sdiff : IsOpen (c.pBall' \ {p}) :=
  c.isOpen_pBall'.sdiff isClosed_singleton

theorem symm_p_eq_zero : c.e.χ.symm p = 0 := by
  have h := congrArg c.e.χ.symm c.e.hχ0
  rw [c.chart_p_symm_eq' (by rw [morseNorm_zero]; nlinarith [c.hε])] at h
  exact h.symm

theorem symm_ne_zero_iff {x : M} (hx : x ∈ c.pBall') : c.e.χ.symm x ≠ 0 ↔ x ≠ p := by
  have hχ : c.e.χ (c.e.χ.symm x) = x := c.e.symm_image_eq (c.pBall'_subset_image_ball hx)
  constructor
  · intro h hxp
    subst hxp
    exact h (symm_p_eq_zero (c := c))
  · intro h h0
    apply h
    rw [← hχ, h0, c.e.hχ0]

/-- Right-local decrease of `L` at a point of the cycle region in the ball of `p`. -/
theorem exists_right_le_L_of_mem_pBall' (hk : k.Good) {x : M} {t : ℝ} (hz : k.Φ t x ∈ k.Ccyc)
    (hp : k.Φ t x ∈ c.pBall') :
    ∃ ε > 0, ∀ s ∈ Icc t (t + ε), c.L (k.Φ s x) ≤ c.L (k.Φ t x) := by
  have h0 := k.symm_ne_zero_of_mem_Ccyc hk hz hp
  have hO : k.Φ t x ∈ c.pBall' \ {p} := ⟨hp, (symm_ne_zero_iff hp).1 h0⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open (isOpen_pBall'_sdiff (c := c)) hO
  refine ⟨ε, hε, fun s hs => ?_⟩
  have hall : ∀ u ∈ Icc t s, k.Φ u x ∈ c.pBall' \ {p} := fun u hu =>
    hεO u ⟨by linarith [hu.1], hu.2.trans hs.2⟩
  have hanti : AntitoneOn (fun u => Bm c.e₁ (c.e.χ.symm (k.Φ u x))) (Icc t s) := by
    refine antitoneOn_Icc_of_hasDerivAt_nonpos
      (g' := fun u => BmDeriv c.e₁ (c.e.χ.symm (k.Φ u x)) (k.Vp (c.e.χ.symm (k.Φ u x))))
      (fun u hu => k.hasDerivAt_Bm_Φ_p (hall u hu).1
        ((symm_ne_zero_iff (hall u hu).1).2 (hall u hu).2))
      (fun u hu => k.BmDeriv_Vp_nonpos (c.symm_sq_lt_of_mem_pBall' (hall u hu).1)
        ((symm_ne_zero_iff (hall u hu).1).2 (hall u hu).2))
  have h1 : Bm c.e₁ (c.e.χ.symm (k.Φ s x)) ≤ Bm c.e₁ (c.e.χ.symm (k.Φ t x)) :=
    hanti (left_mem_Icc.2 hs.1) (right_mem_Icc.2 hs.1) hs.1
  rw [c.L_of_mem_pBall' (hall s (right_mem_Icc.2 hs.1)).1, c.L_of_mem_pBall' hp]
  exact h1

/-- Right-local decrease of `L` at a point of a trajectory segment in the cycle region, in the
ball of `q`. -/
theorem exists_right_le_L_of_mem_qBall' (hk : k.Good) {x : M} {T t : ℝ}
    (hT : ∀ s ∈ Icc 0 T, k.Φ s x ∈ k.Ccyc) (ht : t ∈ Ico 0 T) (hq : k.Φ t x ∈ c.qBall') :
    ∃ ε > 0, ∀ s ∈ Icc t (t + ε), s ≤ T → c.L (k.Φ s x) ≤ c.L (k.Φ t x) := by
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open c.isOpen_qBall' hq
  refine ⟨ε, hε, fun s hs hsT => ?_⟩
  have hall : ∀ u ∈ Icc t s, k.Φ u x ∈ c.qBall' := fun u hu =>
    hεO u ⟨by linarith [hu.1], hu.2.trans hs.2⟩
  have hσ : ∀ u ∈ Icc t s, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ u x)) := fun u hu =>
    k.σ_uq_nonneg_of_mem_Ccyc hk (hT u ⟨ht.1.trans hu.1, hu.2.trans hsT⟩) (hall u hu)
  have hQ := k.Qq_le_of_mem_Ccyc hk (hT t ⟨ht.1, ht.2.le⟩) hq
  have := k.Lq_le_Φ hall hk hσ hQ s (right_mem_Icc.2 hs.1)
  rw [c.L_of_mem_qBall' (hall s (right_mem_Icc.2 hs.1)), c.L_of_mem_qBall' hq]
  exact this

/-- The derivative of `Lσ ∘ ζ` along `Φ` at a time in the middle band. -/
theorem hasDerivAt_Lσ_ζ_Φ (hk : k.Good) {x : M} {u : ℝ} (hu : k.Φ u x ∈ c.TubeOpenσ)
    (h1 : c.lo₂ ≤ f (k.Φ u x)) (h2 : f (k.Φ u x) ≤ c.hi₁) (hζ : ‖c.ζ (k.Φ u x)‖ < hk.δ'') :
    HasDerivAt (fun s => c.Lσ (c.ζ (k.Φ s x)))
      (-(2 * (c.lam * k.βm' (k.Φ u x))) * fderiv ℝ c.Lσ (c.ζ (k.Φ u x)) (c.ζ (k.Φ u x))) u := by
  have h := (hk.hasFDerivAt_Lσ hζ).comp_hasDerivAt u (k.hasDerivAt_ζ_Φ hu.1)
  rw [k.dζ_V'_mid hu h1 h2] at h
  rw [← (hk.hasFDerivAt_Lσ hζ).fderiv, map_smul, smul_eq_mul] at h
  exact h

theorem deriv_Lσ_ζ_nonpos (hk : k.Good) {x : M} {u : ℝ} (hu : k.Φ u x ∈ c.TubeOpenσ)
    (hζ : ‖c.ζ (k.Φ u x)‖ < hk.δ'') :
    -(2 * (c.lam * k.βm' (k.Φ u x))) * fderiv ℝ c.Lσ (c.ζ (k.Φ u x)) (c.ζ (k.Φ u x)) ≤ 0 := by
  have _ := hu
  have h1 := hk.fderiv_Lσ_self_nonneg hζ
  have h2 := k.βm'_nonneg (k.Φ u x)
  have h3 := c.lam_pos
  have : 0 ≤ 2 * (c.lam * k.βm' (k.Φ u x)) * fderiv ℝ c.Lσ (c.ζ (k.Φ u x)) (c.ζ (k.Φ u x)) := by
    positivity
  linarith

/-- Right-local decrease of `L` at a point of a trajectory segment in the cycle region, in the
open middle band. -/
theorem exists_right_le_L_of_mem_Tmid (hk : k.Good) {x : M} {T t : ℝ}
    (hT : ∀ s ∈ Icc 0 T, k.Φ s x ∈ k.Ccyc) (ht : t ∈ Ico 0 T) (hz : k.Φ t x ∈ k.Tmid)
    (hlo : c.lo₂ < f (k.Φ t x)) (hhi : f (k.Φ t x) < c.hi₁) :
    ∃ ε > 0, ∀ s ∈ Icc t (t + ε), s ≤ T → c.L (k.Φ s x) ≤ c.L (k.Φ t x) := by
  have hO : k.Φ t x ∈ c.TubeOpenσ ∩ {w | c.lo₂ < f w ∧ f w < c.hi₁} :=
    ⟨k.Tmid_subset_TubeOpenσ hz, hlo, hhi⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open (c.isOpen_TubeOpenσ.inter
    ((isOpen_lt continuous_const c.hfs.continuous).inter
      (isOpen_lt c.hfs.continuous continuous_const))) hO
  refine ⟨ε, hε, fun s hs hsT => ?_⟩
  have hall : ∀ u ∈ Icc t s, k.Φ u x ∈ k.Tmid := fun u hu => by
    have hO' := hεO u ⟨by linarith [hu.1], hu.2.trans hs.2⟩
    exact k.mem_Tmid_of_mem_Ccyc hk (hT u ⟨ht.1.trans hu.1, hu.2.trans hsT⟩) hO'.2.1 hO'.2.2
  have hζ : ∀ u ∈ Icc t s, ‖c.ζ (k.Φ u x)‖ < hk.δ'' := fun u hu =>
    (k.norm_ζ_le_of_mem_Sσ (hall u hu).1).trans_lt hk.hδ'δ''
  have hanti : AntitoneOn (fun u => c.Lσ (c.ζ (k.Φ u x))) (Icc t s) :=
    antitoneOn_Icc_of_hasDerivAt_nonpos
      (fun u hu => k.hasDerivAt_Lσ_ζ_Φ hk (k.Tmid_subset_TubeOpenσ (hall u hu))
        (hall u hu).2.1 (hall u hu).2.2 (hζ u hu))
      (fun u hu => k.deriv_Lσ_ζ_nonpos hk (k.Tmid_subset_TubeOpenσ (hall u hu)) (hζ u hu))
  have h1 : c.Lσ (c.ζ (k.Φ s x)) ≤ c.Lσ (c.ζ (k.Φ t x)) :=
    hanti (left_mem_Icc.2 hs.1) (right_mem_Icc.2 hs.1) hs.1
  rw [k.L_eq_Lσ_ζ_of_mem_Tmid hk (hall s (right_mem_Icc.2 hs.1)),
    k.L_eq_Lσ_ζ_of_mem_Tmid hk hz]
  exact h1

/-- **`L` is non-increasing along every trajectory segment in the cycle region.** -/
theorem antitoneOn_L_Φ (hk : k.Good) {x : M} {T : ℝ} (hT : ∀ s ∈ Icc 0 T, k.Φ s x ∈ k.Ccyc) :
    AntitoneOn (fun s => c.L (k.Φ s x)) (Icc 0 T) := by
  refine antitoneOn_Icc_of_right_local
    ((k.continuousOn_L_Ccyc hk).comp (k.continuous_Φ_curve x).continuousOn fun s hs => hT s hs)
    fun t ht => ?_
  have hz := hT t (Ico_subset_Icc_self ht)
  by_cases hp : k.Φ t x ∈ c.pBall'
  · obtain ⟨ε, hε, h⟩ := k.exists_right_le_L_of_mem_pBall' hk hz hp
    exact ⟨ε, hε, fun s hs _ => h s ⟨hs.1.le, hs.2⟩⟩
  by_cases hq : k.Φ t x ∈ c.qBall'
  · obtain ⟨ε, hε, h⟩ := k.exists_right_le_L_of_mem_qBall' hk hT ht hq
    exact ⟨ε, hε, fun s hs hsT => h s ⟨hs.1.le, hs.2⟩ hsT⟩
  have hzT : k.Φ t x ∈ k.Tmid := by
    rcases hz with (h | h) | h
    · exact absurd (c.Ann_subset_pBall' h) hp
    · exact h
    · exact absurd (k.RqPos_subset_qBall' hk h) hq
  have hlo : c.lo₂ < f (k.Φ t x) := by
    rcases hzT.2.1.eq_or_lt with h | h
    · exact absurd (c.Ann_subset_pBall' (c.mem_Ann_of_mem_Tmid_lo₂ k hk hzT h.symm)) hp
    · exact h
  have hhi : f (k.Φ t x) < c.hi₁ := by
    rcases hzT.2.2.eq_or_lt with h | h
    · exact absurd (k.RqPos_subset_qBall' hk (c.mem_RqPos_of_mem_Tmid_hi₁ k hk hzT h)) hq
    · exact h
  obtain ⟨ε, hε, h⟩ := k.exists_right_le_L_of_mem_Tmid hk hT ht hzT hlo hhi
  exact ⟨ε, hε, fun s hs hsT => h s ⟨hs.1.le, hs.2⟩ hsT⟩

/-! ### Strict decrease of `L` -/

/-- **Strict decrease in the annulus**: at a point of the annulus in the one-sided tube with
`0 < ‖ζ‖ < δ'`, the angle strictly decreases. -/
theorem exists_L_lt_of_mem_Ann {x : M} (hx : x ∈ c.Ann) (hT : x ∈ c.TubeOpenσ)
    (hζ0 : c.ζ x ≠ 0) (hζ : ‖c.ζ x‖ < k.δ') : ∃ t, 0 < t ∧ c.L (k.Φ t x) < c.L x := by
  have hp := c.Ann_subset_pBall' hx
  have hy0 := c.symm_ne_zero_of_mem_Ann hx
  have hsq := c.symm_sq_lt_of_mem_pBall' hp
  set y := c.e.χ.symm x with hydef
  have hχ : c.e.χ y = x := c.e.symm_image_eq (c.pBall'_subset_image_ball hp)
  have hd := k.hasDerivAt_Bm_Φ_p (x := x) (s := 0) (by rw [k.Φ_zero]; exact hp)
    (by rw [k.Φ_zero]; exact hy0)
  rw [k.Φ_zero] at hd
  -- the derivative is negative
  have hneg : BmDeriv c.e₁ y (k.Vp y) < 0 := by
    rw [k.BmDeriv_Vp hy0]
    have h1 : c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * BmDeriv c.e₁ y c.e₁ ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos
      · exact mul_nonneg c.m'_pos.le (mul_nonneg (βp_nonneg _) (ψp_nonneg _))
      · rw [BmDeriv_e₁ c.morseNorm_e₁ hy0]
        have := perpSq_nonneg c.morseNorm_e₁ y
        have := morseNorm_pos hy0
        have : 0 ≤ perpSq c.e₁ y / morseNorm n y ^ 3 := by positivity
        linarith
    have hBp : 0 < k.Bp y := by
      rw [k.Bp_of_mem (by rw [hχ]; exact hT), hχ]
      have hψ : c.ψm' x = 1 := by
        apply c.ψm'_eq_one
        · rw [c.f_eq_of_mem_pBall' hp]
          have h := (c.symm_mem_of_mem_Ann hx).1
          have h2 := c.ρA_sq_eq
          have h3 := c.ρA_le_ρs
          have := pow_le_pow_left₀ c.ρA_pos.le (h3.trans h) 2
          linarith
        · exact (c.f_le_lo₂_of_mem_Ann hx).trans (by unfold lo₂ hi₂; linarith [c.c₁_lt_c₂])
      rw [hψ, mul_one]
      exact cut_pos_of_lt k.two_δ_sq_lt_δ'_sq (pow_lt_pow_left₀ hζ (norm_nonneg _) two_ne_zero)
    have h2 : BmDeriv c.e₁ y (c.Zp' y) < 0 := by
      rw [c.Zp'_of_mem (by rw [hχ]; exact hT)]
      refine k.hdB y hsq (by rw [hχ]; exact hT) ?_ ?_
      · rw [hχ]; exact norm_pos_iff.2 hζ0
      · rw [hχ]; exact hζ
    have h3 : 2 * (c.lam * k.Bp y) * BmDeriv c.e₁ y (c.Zp' y) < 0 :=
      mul_neg_of_pos_of_neg (by have := c.lam_pos; positivity) h2
    linarith
  have hev := eventually_lt_of_hasDerivAt_neg hneg hd
  have hmem : ∀ᶠ s in 𝓝[>] (0 : ℝ), k.Φ s x ∈ c.pBall' := by
    refine nhdsWithin_le_nhds ?_
    exact (k.continuous_Φ_curve x).continuousAt.preimage_mem_nhds
      (c.isOpen_pBall'.mem_nhds (by rw [k.Φ_zero]; exact hp))
  obtain ⟨t, ⟨hlt, hmem'⟩, ht⟩ := ((hev.and hmem).and self_mem_nhdsWithin).exists
  rw [k.Φ_zero] at hlt
  refine ⟨t, ht, ?_⟩
  rw [c.L_of_mem_pBall' hmem', c.L_of_mem_pBall' hp]
  exact hlt

/-- **Strict decrease in the upper region of `q`**: at a point with `σ u > 0`, `Q > 0`, and an
active pusher or contraction, the transported angle strictly decreases. -/
theorem exists_L_lt_of_mem_RqPos (hk : k.Good) {x : M} (hx : x ∈ k.RqPos)
    (hu : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm x)) (hQ0 : 0 < c.Qq (c.d.χ.symm x))
    (hβ : βq c.d.hk c.hkq k.δ k.τ c.σ (c.d.χ.symm x) *
      ψq c.d.hk c.hkq c.uA c.uB (c.d.χ.symm x) ≠ 0 ∨ k.Bq (c.d.χ.symm x) ≠ 0) :
    ∃ t, 0 < t ∧ c.L (k.Φ t x) < c.L x := by
  have hq := k.RqPos_subset_qBall' hk hx
  have hy := k.symm_mem_RegQPos_of_mem_RqPos hk hx
  set y := c.d.χ.symm x with hydef
  -- the rate of `Q` is negative
  have hrate : k.QRate y < 0 := by
    unfold QRate
    have hv : 0 < ‖posPart c.d.hk y‖ ^ 2 := by
      by_contra h
      push Not at h
      have : ‖posPart c.d.hk y‖ ^ 2 = 0 := le_antisymm h (by positivity)
      have hQ := c.Qq_eq_uq y
      rw [this, mul_zero] at hQ
      linarith
    have hu0 : 0 < uq c.d.hk c.hkq y ^ 2 := by
      have : uq c.d.hk c.hkq y ≠ 0 := fun h => by rw [h, mul_zero] at hu; exact lt_irrefl _ hu
      positivity
    have h1 : 0 ≤ c.σ * uq c.d.hk c.hkq y *
        (c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y)) :=
      mul_nonneg hu.le (mul_nonneg c.m'_pos.le (mul_nonneg (βq_nonneg _ _ _) (ψq_nonneg _ _ _)))
    have h2 : 0 ≤ 2 * (c.lam * k.Bq y) * (c.κ (c.d.χ y) * uq c.d.hk c.hkq y ^ 2) :=
      mul_nonneg (by have := c.lam_pos; have := k.Bq_nonneg y; positivity)
        (mul_nonneg (c.κ_pos _).le (sq_nonneg _))
    have hsum : 0 < c.σ * uq c.d.hk c.hkq y *
        (c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y)) +
        2 * (c.lam * k.Bq y) * (c.κ (c.d.χ y) * uq c.d.hk c.hkq y ^ 2) := by
      rcases hβ with hβ | hβ
      · have : 0 < βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y :=
          lt_of_le_of_ne (mul_nonneg (βq_nonneg _ _ _) (ψq_nonneg _ _ _)) (Ne.symm hβ)
        have := mul_pos hu (mul_pos c.m'_pos this)
        linarith
      · have hB : 0 < k.Bq y := lt_of_le_of_ne (k.Bq_nonneg y) (Ne.symm hβ)
        have := mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) (mul_pos c.lam_pos hB))
          (mul_pos (c.κ_pos (c.d.χ y)) hu0)
        linarith
    nlinarith
  have hd := k.hasDerivAt_Qq_Φ (x := x) (s := 0) (by rw [k.Φ_zero]; exact hq)
  rw [k.Φ_zero] at hd
  have hev := eventually_lt_of_hasDerivAt_neg hrate hd
  have hO : k.Φ 0 x ∈ c.qBall' ∩ {w | 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm w)} := by
    rw [k.Φ_zero]; exact ⟨hq, hu⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open
    (c.isOpen_qBall'_inter (P := fun r => 0 < r) (isOpen_lt continuous_const continuous_id)) hO
  obtain ⟨t, hlt, ht⟩ := (hev.and (Ioc_mem_nhdsGT (show (0:ℝ) < ε from hε))).exists
  have hall : ∀ u ∈ Icc 0 t, k.Φ u x ∈ c.qBall' := fun u hu =>
    (hεO u ⟨by linarith [hu.1], by linarith [hu.2, ht.2]⟩).1
  have hσ : ∀ u ∈ Icc 0 t, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ u x)) := fun u hu =>
    (hεO u ⟨by linarith [hu.1], by linarith [hu.2, ht.2]⟩).2.le
  have hQ' : c.Qq (c.d.χ.symm (k.Φ 0 x)) ≤ k.Q' := by rw [k.Φ_zero]; exact hy.2.2.2
  have hQ0' : 0 < c.Qq (c.d.χ.symm (k.Φ 0 x)) := by rw [k.Φ_zero]; exact hQ0
  have hlt' : c.Qq (c.d.χ.symm (k.Φ t x)) < c.Qq (c.d.χ.symm (k.Φ 0 x)) := hlt
  have := k.Lq_lt_Φ hall hk hσ hQ' hQ0' (right_mem_Icc.2 ht.1.le) hlt'
  rw [k.Φ_zero] at this
  refine ⟨t, ht.1, ?_⟩
  rw [c.L_of_mem_qBall' (hall t (right_mem_Icc.2 ht.1.le)), c.L_of_mem_qBall' hq]
  exact this

/-- **Strict decrease in the open middle band**: at a point of `Tmid` with `lo₂ < f < hi₁` and
`0 < ‖ζ‖ < δ'`, whose forward trajectory stays in the cycle region, `L` strictly decreases. -/
theorem exists_L_lt_of_mem_Tmid (hk : k.Good) {x : M} (hcon : ∀ t, 0 ≤ t → k.Φ t x ∈ k.Ccyc)
    (hx : x ∈ k.Tmid) (hlo : c.lo₂ < f x) (hhi : f x < c.hi₁) (hζ0 : c.ζ x ≠ 0)
    (hζ : ‖c.ζ x‖ < k.δ') : ∃ t, 0 < t ∧ c.L (k.Φ t x) < c.L x := by
  have hT := k.Tmid_subset_TubeOpenσ hx
  have hζ'' : ‖c.ζ x‖ < hk.δ'' := hζ.trans hk.hδ'δ''
  have hd := k.hasDerivAt_Lσ_ζ_Φ hk (x := x) (u := 0) (by rw [k.Φ_zero]; exact hT)
    (by rw [k.Φ_zero]; exact hlo.le) (by rw [k.Φ_zero]; exact hhi.le) (by rw [k.Φ_zero]; exact hζ'')
  rw [k.Φ_zero] at hd
  have hneg : -(2 * (c.lam * k.βm' x)) * fderiv ℝ c.Lσ (c.ζ x) (c.ζ x) < 0 := by
    have h1 := hk.fderiv_Lσ_self_pos hζ0 hζ''
    have h2 : 0 < k.βm' x :=
      cut_pos_of_lt k.two_δ_sq_lt_δ'_sq (pow_lt_pow_left₀ hζ (norm_nonneg _) two_ne_zero)
    have h3 := c.lam_pos
    have : 0 < 2 * (c.lam * k.βm' x) * fderiv ℝ c.Lσ (c.ζ x) (c.ζ x) := by positivity
    linarith
  have hev := eventually_lt_of_hasDerivAt_neg hneg hd
  have hO : k.Φ 0 x ∈ c.TubeOpenσ ∩ {w | c.lo₂ < f w ∧ f w < c.hi₁} := by
    rw [k.Φ_zero]; exact ⟨hT, hlo, hhi⟩
  have hmem : ∀ᶠ s in 𝓝[>] (0 : ℝ), k.Φ s x ∈ c.TubeOpenσ ∩ {w | c.lo₂ < f w ∧ f w < c.hi₁} := by
    refine nhdsWithin_le_nhds ?_
    exact (k.continuous_Φ_curve x).continuousAt.preimage_mem_nhds
      ((c.isOpen_TubeOpenσ.inter ((isOpen_lt continuous_const c.hfs.continuous).inter
        (isOpen_lt c.hfs.continuous continuous_const))).mem_nhds hO)
  obtain ⟨t, ⟨hlt, hmem'⟩, ht⟩ := ((hev.and hmem).and self_mem_nhdsWithin).exists
  rw [k.Φ_zero] at hlt
  have htT : k.Φ t x ∈ k.Tmid := k.mem_Tmid_of_mem_Ccyc hk (hcon t ht.le) hmem'.2.1 hmem'.2.2
  refine ⟨t, ht, ?_⟩
  rw [k.L_eq_Lσ_ζ_of_mem_Tmid hk htT, k.L_eq_Lσ_ζ_of_mem_Tmid hk hx]
  exact hlt


/-! ### The strictness set and the LaSalle exit from the cycle region -/

/-- The set where `L` is not claimed to strictly decrease. -/
def Zc : Set M :=
  {x | x ∈ c.Ann ∧ (x ∉ c.TubeOpenσ ∨ c.ζ x = 0 ∨ k.δ' ≤ ‖c.ζ x‖)} ∪
  {x | x ∈ k.Tmid ∧ (c.ζ x = 0 ∨ k.δ' ≤ ‖c.ζ x‖)} ∪
  {x | x ∈ k.RqPos ∧ (c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) = 0 ∨ c.Qq (c.d.χ.symm x) = 0 ∨
    (βq c.d.hk c.hkq k.δ k.τ c.σ (c.d.χ.symm x) * ψq c.d.hk c.hkq c.uA c.uB (c.d.χ.symm x) = 0 ∧
      k.Bq (c.d.χ.symm x) = 0))}

/-- **Strict decrease off `Zc`.** -/
theorem exists_L_lt_of_notMem_Zc (hk : k.Good) {x : M} (hx : x ∈ k.Ccyc) (hZ : x ∉ k.Zc)
    (hcon : ∀ t, 0 ≤ t → k.Φ t x ∈ k.Ccyc) : ∃ t, 0 < t ∧ c.L (k.Φ t x) < c.L x := by
  by_cases hA : x ∈ c.Ann
  · have h : ¬ (x ∉ c.TubeOpenσ ∨ c.ζ x = 0 ∨ k.δ' ≤ ‖c.ζ x‖) := fun h =>
      hZ (Or.inl (Or.inl ⟨hA, h⟩))
    push Not at h
    exact k.exists_L_lt_of_mem_Ann hA h.1 h.2.1 h.2.2
  by_cases hR : x ∈ k.RqPos
  · have h : ¬ (c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) = 0 ∨ c.Qq (c.d.χ.symm x) = 0 ∨
        (βq c.d.hk c.hkq k.δ k.τ c.σ (c.d.χ.symm x) *
          ψq c.d.hk c.hkq c.uA c.uB (c.d.χ.symm x) = 0 ∧ k.Bq (c.d.χ.symm x) = 0)) :=
      fun h => hZ (Or.inr ⟨hR, h⟩)
    push Not at h
    have hy := k.symm_mem_RegQPos_of_mem_RqPos hk hR
    have hu : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) := lt_of_le_of_ne hy.1 (Ne.symm h.1)
    have hQ : 0 < c.Qq (c.d.χ.symm x) := lt_of_le_of_ne (c.Qq_nonneg _) (Ne.symm h.2.1)
    refine k.exists_L_lt_of_mem_RqPos hk hR hu hQ ?_
    by_cases hβ : βq c.d.hk c.hkq k.δ k.τ c.σ (c.d.χ.symm x) *
        ψq c.d.hk c.hkq c.uA c.uB (c.d.χ.symm x) = 0
    · exact Or.inr (h.2.2 hβ)
    · exact Or.inl hβ
  have hT : x ∈ k.Tmid := by
    rcases hx with (h | h) | h
    · exact absurd h hA
    · exact h
    · exact absurd h hR
  have hlo : c.lo₂ < f x := by
    rcases hT.2.1.eq_or_lt with h | h
    · exact absurd (c.mem_Ann_of_mem_Tmid_lo₂ k hk hT h.symm) hA
    · exact h
  have hhi : f x < c.hi₁ := by
    rcases hT.2.2.eq_or_lt with h | h
    · exact absurd (c.mem_RqPos_of_mem_Tmid_hi₁ k hk hT h) hR
    · exact h
  have h : ¬ (c.ζ x = 0 ∨ k.δ' ≤ ‖c.ζ x‖) := fun h => hZ (Or.inl (Or.inr ⟨hT, h⟩))
  push Not at h
  exact k.exists_L_lt_of_mem_Tmid hk hcon hT hlo hhi h.1 h.2

/-- A point of `Tmid` at the level `lo₂` in the one-sided tube with `0 < ‖ζ‖ < δ'` is off
`Zc`. -/
theorem notMem_Zc_of_lo₂ (hk : k.Good) {w : M} (hw : w ∈ k.Tmid) (hf : f w = c.lo₂)
    (hζ0 : c.ζ w ≠ 0) (hζ : ‖c.ζ w‖ < k.δ') : w ∉ k.Zc := by
  have hT := k.Tmid_subset_TubeOpenσ hw
  rintro ((⟨-, h⟩ | ⟨-, h⟩) | ⟨h, -⟩)
  · rcases h with h | h | h
    · exact h hT
    · exact hζ0 h
    · linarith
  · rcases h with h | h
    · exact hζ0 h
    · linarith
  · have := k.f_ge_lo₂_of_mem_RqPos hk h
    have := k.hi₁_le_f_of_mem_Rq hk (k.RqPos_subset_Rq h)
    linarith [c.lo₂_lt_hi₁]

/-- A point of `Tmid` at the level `hi₁` with `0 < ‖ζ‖ < δ'` is off `Zc`. -/
theorem notMem_Zc_of_hi₁ (hk : k.Good) {w : M} (hw : w ∈ k.Tmid) (hf : f w = c.hi₁)
    (hζ0 : c.ζ w ≠ 0) (hζ : ‖c.ζ w‖ < k.δ') : w ∉ k.Zc := by
  have hT := k.Tmid_subset_TubeOpenσ hw
  rintro ((⟨h, -⟩ | ⟨-, h⟩) | ⟨hR, h⟩)
  · have := c.f_le_lo₂_of_mem_Ann h
    linarith [c.lo₂_lt_hi₁]
  · rcases h with h | h
    · exact hζ0 h
    · linarith
  · have hq := k.RqPos_subset_qBall' hk hR
    have hχ : c.d.χ (c.d.χ.symm w) = w := c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
    have hsq := c.symm_sq_lt_of_mem_qBall' hq
    have hu := k.σ_uq_pos_of_mem_Tmid hw hq
    rcases h with h | h | h
    · linarith
    · apply hζ0
      rw [← hχ, c.ζ_eq_ζhat hsq (by rw [hχ]; exact hT.1)]
      exact (c.ζhat_eq_zero_iff _).2 h
    · have hB : k.Bq (c.d.χ.symm w) ≠ 0 := by
        rw [k.Bq_of_mem (by rw [hχ]; exact hT), hχ]
        have hψ : c.ψm' w = 1 := c.ψm'_eq_one
          (by rw [hf]; linarith [c.lo₁_lt_lo₂, c.lo₂_lt_hi₁]) (by rw [hf]; exact c.hi₁_lt_hi₂.le)
        rw [hψ, mul_one]
        exact (cut_pos_of_lt k.two_δ_sq_lt_δ'_sq
          (pow_lt_pow_left₀ hζ (norm_nonneg _) two_ne_zero)).ne'
      exact hB h.2

/-- The property "eventually outside `Ccyc ∩ Zc`". -/
def Leaves (z : M) : Prop := ∃ t, 0 ≤ t ∧ k.Φ t z ∉ k.Ccyc ∩ k.Zc

theorem leaves_of_f_le (hk : k.Good) {z : M} {T : ℝ} (hT : 0 ≤ T) (hf : f (k.Φ T z) ≤ a') :
    k.Leaves z :=
  ⟨T, hT, fun h => k.notMem_Ccyc_of_f_le hk hf h.1⟩

theorem leaves_of_notMem_Zc {z : M} {t : ℝ} (ht : 0 ≤ t) (hZ : k.Φ t z ∉ k.Zc) : k.Leaves z :=
  ⟨t, ht, fun h => hZ h.2⟩

theorem leaves_shift {z : M} {t : ℝ} (ht : 0 ≤ t) (h : k.Leaves (k.Φ t z)) : k.Leaves z := by
  obtain ⟨T, hT, hTz⟩ := h
  exact ⟨t + T, by linarith, by rw [k.Φ_add]; exact hTz⟩

/-- A point of `Tmid` at the level `hi₁` on the arc lies on the axis segment of `q`. -/
theorem mem_Ax_of_mem_Tmid_hi₁ (hk : k.Good) {z : M} (hz : z ∈ k.Tmid) (hf : f z = c.hi₁)
    (hζ : c.ζ z = 0) : z ∈ c.Ax := by
  have hR := c.mem_RqPos_of_mem_Tmid_hi₁ k hk hz hf
  have hq := k.RqPos_subset_qBall' hk hR
  have hχ : c.d.χ (c.d.χ.symm z) = z := c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
  have hsq := c.symm_sq_lt_of_mem_qBall' hq
  have hT := k.Tmid_subset_TubeOpenσ hz
  refine k.mem_Ax_of_mem_RqPos hk hR ?_
  have hQ : c.Qq (c.d.χ.symm z) = 0 := by
    rw [← c.ζhat_eq_zero_iff, ← c.ζ_eq_ζhat hsq (by rw [hχ]; exact hT.1), hχ]
    exact hζ
  have hu := k.σ_uq_pos_of_mem_Tmid hz hq
  rw [c.Qq_eq_uq] at hQ
  rcases mul_eq_zero.1 hQ with h | h
  · exfalso
    have : uq c.d.hk c.hkq (c.d.χ.symm z) = 0 := pow_eq_zero_iff two_ne_zero |>.1 h
    rw [this, mul_zero] at hu
    exact lt_irrefl _ hu
  · exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)

/-- **The arc leaves**: a point of `Tmid` with `ζ = 0` reaches the axis of `q`, which descends
below `a'`. -/
theorem leaves_of_mem_Tmid_ζ_zero (hk : k.Good) {z : M} (hz : z ∈ k.Tmid) (hζ : c.ζ z = 0) :
    k.Leaves z := by
  obtain ⟨t, ht, hT, hf, hζ'⟩ := k.exists_reach_hi₁_of_ζ_eq_zero hz hζ
  refine k.leaves_shift ht ?_
  obtain ⟨T, hT', hfT⟩ := k.exists_f_le_a'_of_mem_Ax hk (k.mem_Ax_of_mem_Tmid_hi₁ hk hT hf hζ')
  exact k.leaves_of_f_le hk hT' hfT

/-- **The ball region leaves**: through `Wp2 ∩ Tmid`. -/
theorem leaves_of_mem_Wball (hk : k.Good) {z : M} (hz : z ∈ c.Wball) : k.Leaves z := by
  obtain ⟨t, ht, hW2, hT, hf⟩ := k.exists_reach_Wp2_Tmid hk hz
  refine k.leaves_shift ht ?_
  set w := k.Φ t z with hw
  have hWb := k.Wp2_subset_Wball hW2
  obtain ⟨h1, h2, h3⟩ := (k.mem_Wp2_iff (c.Wball_subset_image_ball hWb)).1 hW2
  obtain ⟨hTσ, hζ⟩ := k.mem_tube_of_Bm_le h1 h2 h3
  rw [c.e.symm_image_eq (c.Wball_subset_image_ball hWb)] at hTσ hζ
  by_cases hζ0 : c.ζ w = 0
  · exact k.leaves_of_mem_Tmid_ζ_zero hk hT hζ0
  · exact k.leaves_of_notMem_Zc le_rfl (by rw [k.Φ_zero]; exact k.notMem_Zc_of_lo₂ hk hT hf hζ0 hζ)

/-- **The outer part of the band leaves**: a point of `Tmid` with `‖ζ‖ ≥ δ'` moves down. -/
theorem leaves_of_mem_Tmid_δ' (hk : k.Good) {z : M} (hz : z ∈ k.Tmid) (hζ : k.δ' ≤ ‖c.ζ z‖) :
    k.Leaves z := by
  rcases hz.2.1.eq_or_lt with hlo | hlo
  · exact k.leaves_of_mem_Wball hk (c.Ann_subset_Wball (c.mem_Ann_of_mem_Tmid_lo₂ k hk hz hlo.symm))
  obtain ⟨t₀, ht₀, hz₁, hf₁, hlo₁⟩ :=
    k.exists_pos_mem_Tmid_of_two_δ_le hz (by linarith [k.hδδ']) hlo
  refine k.leaves_shift ht₀.le ?_
  set z₁ := k.Φ t₀ z with hz₁def
  obtain ⟨t, ht, hall, -, hexit⟩ := k.exists_exit_mid_band hz₁
  refine k.leaves_shift ht ?_
  set z₂ := k.Φ t z₁ with hz₂def
  have hz₂ : z₂ ∈ k.Tmid := hall t (right_mem_Icc.2 ht)
  rcases hexit with ⟨hf, hζ2⟩ | hf
  · have htpos : 0 < t := by
      rcases ht.eq_or_lt with h | h
      · exfalso
        have hz₂₁ : z₂ = z₁ := by rw [hz₂def, ← h, k.Φ_zero]
        rw [hz₂₁] at hf
        linarith [hz.2.2]
      · exact h
    have hζ' : ‖c.ζ z₂‖ < k.δ' := (hζ2 htpos).trans (by linarith [k.hδδ'])
    by_cases hζ0 : c.ζ z₂ = 0
    · exact k.leaves_of_mem_Tmid_ζ_zero hk hz₂ hζ0
    · exact k.leaves_of_notMem_Zc le_rfl
        (by rw [k.Φ_zero]; exact k.notMem_Zc_of_hi₁ hk hz₂ hf hζ0 hζ')
  · exact k.leaves_of_mem_Wball hk (c.Ann_subset_Wball (c.mem_Ann_of_mem_Tmid_lo₂ k hk hz₂ hf))

/-- **The upper region of `q` leaves.** -/
theorem leaves_of_mem_RqPos (hk : k.Good) {z : M} (hz : z ∈ k.RqPos) : k.Leaves z := by
  obtain ⟨t, ht, hall, hface⟩ := k.exists_exit_RqPos_face hk hz
  rcases hface with hu | ⟨hf, hT, -, -⟩
  · obtain ⟨T, hT, hfT⟩ :=
      k.exists_f_le_a'_of_mem_Rq_face hk (hall t (right_mem_Icc.2 ht)) hu
    exact k.leaves_shift ht (k.leaves_of_f_le hk hT hfT)
  · refine k.leaves_shift ht ?_
    set z₂ := k.Φ t z with hz₂def
    by_cases hζ0 : c.ζ z₂ = 0
    · exact k.leaves_of_mem_Tmid_ζ_zero hk hT hζ0
    rcases (k.norm_ζ_le_of_mem_Sσ hT.1).lt_or_eq with hlt | heq
    · exact k.leaves_of_notMem_Zc le_rfl
        (by rw [k.Φ_zero]; exact k.notMem_Zc_of_hi₁ hk hT hf hζ0 hlt)
    · exact k.leaves_of_mem_Tmid_δ' hk hT heq.ge

/-- **The middle band leaves.** -/
theorem leaves_of_mem_Tmid (hk : k.Good) {z : M} (hz : z ∈ k.Tmid) : k.Leaves z := by
  by_cases hζ0 : c.ζ z = 0
  · exact k.leaves_of_mem_Tmid_ζ_zero hk hz hζ0
  rcases (k.norm_ζ_le_of_mem_Sσ hz.1).lt_or_eq with hlt | heq
  · rcases hz.2.1.eq_or_lt with hlo | hlo
    · exact k.leaves_of_notMem_Zc le_rfl
        (by rw [k.Φ_zero]; exact k.notMem_Zc_of_lo₂ hk hz hlo.symm hζ0 hlt)
    rcases hz.2.2.eq_or_lt with hhi | hhi
    · exact k.leaves_of_notMem_Zc le_rfl
        (by rw [k.Φ_zero]; exact k.notMem_Zc_of_hi₁ hk hz hhi hζ0 hlt)
    refine k.leaves_of_notMem_Zc le_rfl ?_
    rw [k.Φ_zero]
    rintro ((⟨h, -⟩ | ⟨-, h⟩) | ⟨h, -⟩)
    · exact absurd (c.f_le_lo₂_of_mem_Ann h) (not_le.2 hlo)
    · rcases h with h | h
      · exact hζ0 h
      · linarith
    · exact absurd (k.hi₁_le_f_of_mem_Rq hk (k.RqPos_subset_Rq h)) (not_le.2 hhi)
  · exact k.leaves_of_mem_Tmid_δ' hk hz heq.ge

/-- **Every point of the cycle region eventually leaves `Ccyc ∩ Zc`.** -/
theorem leaves_of_mem_Ccyc (hk : k.Good) {z : M} (hz : z ∈ k.Ccyc) : k.Leaves z := by
  rcases hz with (h | h) | h
  · exact k.leaves_of_mem_Wball hk (c.Ann_subset_Wball h)
  · exact k.leaves_of_mem_Tmid hk h
  · exact k.leaves_of_mem_RqPos hk h

/-- **Exit from the cycle region** (LaSalle with the transported angle). -/
theorem exists_exit_Ccyc (hk : k.Good) : ∀ x ∈ k.Ccyc, ∃ t, 0 ≤ t ∧ k.Φ t x ∉ k.Ccyc :=
  k.exists_exit_of_antitone_weak (k.isCompact_Ccyc hk) (k.continuousOn_L_Ccyc hk)
    (Z := k.Zc) (fun _ _ hT => k.antitoneOn_L_Φ hk hT)
    (fun _ hx hcon => k.exists_L_lt_of_notMem_Zc hk hx.1 hx.2 hcon)
    (fun z hz => by
      obtain ⟨t, -, h⟩ := k.leaves_of_mem_Ccyc hk hz.1
      exact ⟨t, h⟩)


/-! ### Local forward invariance of the cycle region until its faces -/

/-- The exit faces of the cycle region: the inner sphere of the annulus and the stable disc
`σ u = 0` of the upper region of `q`. -/
def Fc : Set M := c.e.χ '' {y | morseNorm n y = c.ρs} ∪ (k.RqPos ∩ c.FqMid)

theorem isClosed_Fc (hk : k.Good) : IsClosed k.Fc :=
  (c.e.isCompact_image_of_subset ((isCompact_morseNorm_le c.ρs).of_isClosed_subset
    (isClosed_eq continuous_morseNorm continuous_const) fun _ hy => le_of_eq hy)
    (c.ρs_lt_ρB.trans c.ρB_lt_R') fun _ hy => le_of_eq hy).isClosed.union
    ((k.isCompact_RqPos hk).isClosed.inter c.isClosed_FqMid)

theorem ρs_sq_lt : c.ρs ^ 2 < 3 * c.ε :=
  (pow_lt_pow_left₀ c.ρs_lt_ρB c.ρs_pos.le two_ne_zero).trans c.ρB_sq_lt_three_ε

theorem isOpen_annulus_open :
    IsOpen (c.e.χ '' {y | c.ρs < morseNorm n y ∧ morseNorm n y < c.ρB}) := by
  refine (OpenPartialHomeomorph.isOpen_image_iff_of_subset_source c.e.χ fun y hy => ?_).2 ?_
  · exact c.e.hball (mem_ball_of_morseNorm_lt (hy.2.trans c.ρB_lt_R'))
  · exact (isOpen_lt continuous_const continuous_morseNorm).inter
      (isOpen_lt continuous_morseNorm continuous_const)

/-- From an eventual property on `𝓝[>] 0`, a positive `ε` on which it holds on `Ioc 0 ε`. -/
theorem exists_Ioc_of_eventually {P : ℝ → Prop} (h : ∀ᶠ u in 𝓝[>] (0 : ℝ), P u) :
    ∃ ε > 0, ∀ u ∈ Ioc 0 ε, P u := by
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 h
  exact ⟨ε, hε, fun u hu => hsub hu⟩

/-- Local invariance at an interior point of the annulus. -/
theorem local_Ann_open {z : M} (hz : z ∈ c.Ann) (h1 : c.ρs < morseNorm n (c.e.χ.symm z))
    (h2 : morseNorm n (c.e.χ.symm z) < c.ρB) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.Φ u z ∈ k.Ccyc := by
  have hO : k.Φ 0 z ∈ c.e.χ '' {y | c.ρs < morseNorm n y ∧ morseNorm n y < c.ρB} := by
    rw [k.Φ_zero]
    exact c.e.mem_image_of_symm_mem (c.pBall'_subset_image_ball (c.Ann_subset_pBall' hz))
      ⟨h1, h2⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open (isOpen_annulus_open (c := c)) hO
  refine ⟨ε, hε, fun u hu => ?_⟩
  obtain ⟨y, hy, hyu⟩ := hεO u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  exact k.Ann_subset_Ccyc ⟨y, ⟨hy.1.le, hy.2.le⟩, hyu⟩

/-- Local invariance at a point of the outer sphere outside the reversal zone. -/
theorem local_Ann_sphere_out {z : M} (hz : z ∈ c.Ann) (hr : morseNorm n (c.e.χ.symm z) = c.ρB)
    (hout : z ∈ c.TubeOpenσ → 2 * k.δ ≤ ‖c.ζ z‖) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.Φ u z ∈ k.Ccyc := by
  have hp := c.Ann_subset_pBall' hz
  set y := c.e.χ.symm z with hydef
  have hχ : c.e.χ y = z := c.e.symm_image_eq (c.pBall'_subset_image_ball hp)
  have hsq := c.symm_sq_lt_of_mem_pBall' hp
  have hdot : dot y (k.Vp y) < 0 := by
    rw [k.dot_Vp hsq, k.Cp_eq_zero_of_norm_ζ (by rw [hχ]; exact hout),
      ψp_eq_zero c.ρA_pos.le c.ρA_lt_ρB hr.ge]
    have hθ := ModelField.theta_pos c.e.hr₀ y
    have : 0 < morseNorm n y ^ 2 := by rw [hr]; exact pow_pos c.ρB_pos 2
    nlinarith [mul_pos hθ this]
  have hd := k.hasDerivAt_morseNormSq_Φ_p (x := z) (s := 0) (by rw [k.Φ_zero]; exact hp)
  rw [k.Φ_zero] at hd
  have hev := eventually_lt_of_hasDerivAt_neg (by linarith : 2 * dot y (k.Vp y) < 0) hd
  have hO : k.Φ 0 z ∈ c.e.χ '' {y | c.ρs < morseNorm n y ∧ morseNorm n y ^ 2 < 3 * c.ε} := by
    rw [k.Φ_zero]
    exact c.e.mem_image_of_symm_mem (c.pBall'_subset_image_ball hp)
      ⟨by rw [hr]; exact c.ρs_lt_ρB, hsq⟩
  obtain ⟨ε₁, hε₁, hεO⟩ := k.exists_Icc_Φ_mem_open c.isOpen_annulus_gt hO
  obtain ⟨ε₂, hε₂, hsub⟩ := exists_Ioc_of_eventually hev
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun u hu => ?_⟩
  rcases hu.1.eq_or_lt with h | h
  · rw [← h, k.Φ_zero]; exact k.Ann_subset_Ccyc hz
  · have hu1 : u ≤ ε₁ := hu.2.trans (min_le_left _ _)
    have hu2 : u ≤ ε₂ := hu.2.trans (min_le_right _ _)
    obtain ⟨y', hy', hy'u⟩ := hεO u ⟨by linarith, by linarith [hu1]⟩
    have hlt := hsub u ⟨h, hu2⟩
    have hy'eq : c.e.χ.symm (k.Φ u z) = y' := by rw [← hy'u, c.chart_p_symm_eq' hy'.2]
    rw [hy'eq, k.Φ_zero, ← hydef, hr] at hlt
    have hlt' : morseNorm n y' < c.ρB :=
      (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg _) c.ρB_pos.le two_ne_zero).1 hlt
    exact k.Ann_subset_Ccyc ⟨y', ⟨hy'.1.le, hlt'.le⟩, hy'u⟩

theorem c₁_sub_half_lt_lo₂ : c.c₁ - c.η / 2 < c.lo₂ := by unfold lo₂; linarith [c.η_pos]

/-- Local invariance at a point of the outer sphere inside the reversal zone. -/
theorem local_Ann_sphere_tube (hk : k.Good) {z : M} (hz : z ∈ c.Ann)
    (hr : morseNorm n (c.e.χ.symm z) = c.ρB) (hT : z ∈ c.TubeOpenσ) (hζ : ‖c.ζ z‖ < 2 * k.δ) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.Φ u z ∈ k.Ccyc := by
  have hp := c.Ann_subset_pBall' hz
  have hfz : f z = c.lo₂ := by
    rw [c.f_eq_of_mem_pBall' hp, hr, c.ρB_sq_eq]; ring
  set O : Set M := c.TubeOpenσ ∩ (c.TubeOpen ∩ c.ζ ⁻¹' {v | ‖v‖ < k.δ'}) ∩
    {w | c.c₁ - c.η / 2 < f w ∧ f w < c.hi₁} ∩
    c.e.χ '' {y | c.ρs < morseNorm n y ∧ morseNorm n y ^ 2 < 3 * c.ε} with hOdef
  have hOo : IsOpen O :=
    ((c.isOpen_TubeOpenσ.inter (c.continuousOn_ζ.isOpen_inter_preimage c.isOpen_TubeOpen
      (isOpen_lt continuous_norm continuous_const))).inter
      ((isOpen_lt continuous_const c.hfs.continuous).inter
        (isOpen_lt c.hfs.continuous continuous_const))).inter c.isOpen_annulus_gt
  have hzO : k.Φ 0 z ∈ O := by
    rw [k.Φ_zero]
    refine ⟨⟨⟨hT, hT.1, hζ.trans (by linarith [k.hδδ'])⟩, ?_, ?_⟩, ?_⟩
    · rw [hfz]; exact (c₁_sub_half_lt_lo₂ (c := c))
    · rw [hfz]; exact c.lo₂_lt_hi₁
    · exact c.e.mem_image_of_symm_mem (c.pBall'_subset_image_ball hp)
        ⟨by rw [hr]; exact c.ρs_lt_ρB, c.symm_sq_lt_of_mem_pBall' hp⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open hOo hzO
  refine ⟨ε, hε, fun u hu => ?_⟩
  obtain ⟨⟨⟨hwT, -, hwζ⟩, hw1, hw2⟩, hwA⟩ := hεO u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hwζ' : ‖c.ζ (k.Φ u z)‖ < k.δ' := hwζ
  have hwS : k.Φ u z ∈ k.Sσ :=
    k.mem_Sσ_iff.2 ⟨hwT, ⟨hw1.le, hw2.le.trans c.hi₁_mem_levels⟩, hwζ'.le⟩
  rcases le_or_gt c.lo₂ (f (k.Φ u z)) with h | h
  · exact k.Tmid_subset_Ccyc ⟨hwS, h, hw2.le⟩
  · have hW := hk.Sσ_low_subset_Wball ⟨hwS, h.le⟩
    obtain ⟨y', hy', hy'u⟩ := hwA
    refine k.Ann_subset_Ccyc ⟨y', ⟨hy'.1.le, ?_⟩, hy'u⟩
    have := c.symm_mem_of_mem_Wball hW
    rwa [← hy'u, c.chart_p_symm_eq' hy'.2] at this

/-- Local invariance at a point of the annulus off the inner sphere. -/
theorem local_Ann (hk : k.Good) {z : M} (hz : z ∈ c.Ann) (hF : z ∉ k.Fc) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.Φ u z ∈ k.Ccyc := by
  obtain ⟨h1, h2⟩ := c.symm_mem_of_mem_Ann hz
  have hp := c.Ann_subset_pBall' hz
  have h1' : c.ρs < morseNorm n (c.e.χ.symm z) := by
    rcases h1.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hF
      exact Or.inl (c.e.mem_image_of_symm_mem (c.pBall'_subset_image_ball hp) h.symm)
  rcases h2.lt_or_eq with h | h
  · exact k.local_Ann_open hz h1' h
  · by_cases hin : z ∈ c.TubeOpenσ ∧ ‖c.ζ z‖ < 2 * k.δ
    · exact k.local_Ann_sphere_tube hk hz h hin.1 hin.2
    · refine k.local_Ann_sphere_out hz h fun hT => ?_
      by_contra hlt
      exact hin ⟨hT, not_le.1 hlt⟩

/-- Local invariance at a point of the open middle band. -/
theorem local_Tmid_open {z : M} (hz : z ∈ k.Tmid) (hlo : c.lo₂ < f z) (hhi : f z < c.hi₁) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.Φ u z ∈ k.Ccyc := by
  have hO : k.Φ 0 z ∈ c.TubeOpenσ ∩ {w | c.lo₂ < f w ∧ f w < c.hi₁} := by
    rw [k.Φ_zero]; exact ⟨k.Tmid_subset_TubeOpenσ hz, hlo, hhi⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open (c.isOpen_TubeOpenσ.inter
    ((isOpen_lt continuous_const c.hfs.continuous).inter
      (isOpen_lt c.hfs.continuous continuous_const))) hO
  refine ⟨ε, hε, fun u hu => ?_⟩
  have hband : ∀ v ∈ Icc 0 u, k.Φ v z ∈ c.TubeOpenσ ∧ c.lo₂ ≤ f (k.Φ v z) ∧
      f (k.Φ v z) ≤ c.hi₁ := fun v hv => by
    have := hεO v ⟨by linarith [hv.1], by linarith [hv.2, hu.2]⟩
    exact ⟨this.1, this.2.1.le, this.2.2.le⟩
  exact k.Tmid_subset_Ccyc
    (k.Φ_mem_Tmid_of_band (k.norm_ζ_le_of_mem_Sσ hz.1) hband u (right_mem_Icc.2 hu.1))

/-- The chart conditions preserved along a short segment in the ball of `q` with `σ u > 0`. -/
theorem RqPos_conditions (hk : k.Good) {z : M} (hz : z ∈ k.RqPos) {u : ℝ}
    (hq : ∀ v ∈ Icc 0 u, k.Φ v z ∈ c.qBall')
    (hσ : ∀ v ∈ Icc 0 u, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ v z))) (hu : 0 ≤ u) :
    ‖posPart c.d.hk (c.d.χ.symm (k.Φ u z))‖ ≤ k.ν ∧ c.Qq (c.d.χ.symm (k.Φ u z)) ≤ k.Q' := by
  have hy := k.symm_mem_RegQPos_of_mem_RqPos hk hz
  constructor
  · have hanti := k.antitoneOn_normSq_posPart_Φ hq
    have h1 : ‖posPart c.d.hk (c.d.χ.symm (k.Φ u z))‖ ^ 2 ≤
        ‖posPart c.d.hk (c.d.χ.symm (k.Φ 0 z))‖ ^ 2 :=
      hanti (left_mem_Icc.2 hu) (right_mem_Icc.2 hu) hu
    rw [k.Φ_zero] at h1
    have h2 : ‖posPart c.d.hk (c.d.χ.symm z)‖ ^ 2 ≤ k.ν ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hy.2.2.1 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.ν_pos.le two_ne_zero).1 (h1.trans h2)
  · have hanti := k.antitoneOn_Qq_Φ hq hσ
    have h1 : c.Qq (c.d.χ.symm (k.Φ u z)) ≤ c.Qq (c.d.χ.symm (k.Φ 0 z)) :=
      hanti (left_mem_Icc.2 hu) (right_mem_Icc.2 hu) hu
    rw [k.Φ_zero] at h1
    exact h1.trans hy.2.2.2

/-- Local invariance at a point of the upper region of `q` above the level `hi₁`. -/
theorem local_RqPos_open (hk : k.Good) {z : M} (hz : z ∈ k.RqPos)
    (hu : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm z)) (hf : c.hi₁ < f z) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.Φ u z ∈ k.Ccyc := by
  have hO : k.Φ 0 z ∈ c.qBall' ∩ {w | 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm w)} ∩
      {w | c.hi₁ < f w} := by
    rw [k.Φ_zero]; exact ⟨⟨k.RqPos_subset_qBall' hk hz, hu⟩, hf⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open
    ((c.isOpen_qBall'_inter (P := fun r => 0 < r) (isOpen_lt continuous_const continuous_id)).inter
      (isOpen_lt continuous_const c.hfs.continuous)) hO
  refine ⟨ε, hε, fun u hu => ?_⟩
  have hq : ∀ v ∈ Icc 0 u, k.Φ v z ∈ c.qBall' := fun v hv =>
    (hεO v ⟨by linarith [hv.1], by linarith [hv.2, hu.2]⟩).1.1
  have hσ : ∀ v ∈ Icc 0 u, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ v z)) := fun v hv =>
    (hεO v ⟨by linarith [hv.1], by linarith [hv.2, hu.2]⟩).1.2.le
  obtain ⟨hν, hQ⟩ := k.RqPos_conditions hk hz hq hσ hu.1
  obtain ⟨⟨huq, huσ⟩, huf⟩ := hεO u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have huf' : c.hi₁ < f (k.Φ u z) := huf
  refine k.RqPos_subset_Ccyc (k.mem_RqPos_of_symm huq ⟨huσ.le, ?_, hν, hQ⟩)
  rw [← c.hi₁_le_iff (c.morseNorm_le_R_of_sq_lt (c.symm_sq_lt_of_mem_qBall' huq)),
    c.d.symm_image_eq (c.qBall'_subset_image_ball huq)]
  exact huf'.le

/-- Local invariance at a point of the upper region of `q` at the level `hi₁`. -/
theorem local_RqPos_hi₁ (hk : k.Good) {z : M} (hz : z ∈ k.RqPos)
    (hu : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm z)) (hf : f z = c.hi₁) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.Φ u z ∈ k.Ccyc := by
  have hzq := k.RqPos_subset_qBall' hk hz
  have hχ : c.d.χ (c.d.χ.symm z) = z := c.d.symm_image_eq (c.qBall'_subset_image_ball hzq)
  obtain ⟨-, hT⟩ := k.hi₁_face hk (k.symm_mem_RegQ_of_mem_Rq hk (k.RqPos_subset_Rq hz))
    (by rw [hχ]; exact hf)
  rw [hχ] at hT
  have hO : k.Φ 0 z ∈ c.qBall' ∩ {w | 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm w)} ∩
      c.TubeOpenσ ∩ {w | c.lo₂ < f w} := by
    rw [k.Φ_zero]; exact ⟨⟨⟨hzq, hu⟩, hT⟩, show c.lo₂ < f z by rw [hf]; exact c.lo₂_lt_hi₁⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_Φ_mem_open
    (((c.isOpen_qBall'_inter (P := fun r => 0 < r)
      (isOpen_lt continuous_const continuous_id)).inter c.isOpen_TubeOpenσ).inter
      (isOpen_lt continuous_const c.hfs.continuous)) hO
  refine ⟨ε, hε, fun u hu => ?_⟩
  have hq : ∀ v ∈ Icc 0 u, k.Φ v z ∈ c.qBall' := fun v hv =>
    (hεO v ⟨by linarith [hv.1], by linarith [hv.2, hu.2]⟩).1.1.1
  have hσ : ∀ v ∈ Icc 0 u, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.Φ v z)) := fun v hv =>
    (hεO v ⟨by linarith [hv.1], by linarith [hv.2, hu.2]⟩).1.1.2.le
  obtain ⟨hν, hQ⟩ := k.RqPos_conditions hk hz hq hσ hu.1
  obtain ⟨⟨⟨huq, huσ⟩, huT⟩, hulo⟩ := hεO u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hulo' : c.lo₂ < f (k.Φ u z) := hulo
  have hχu : c.d.χ (c.d.χ.symm (k.Φ u z)) = k.Φ u z :=
    c.d.symm_image_eq (c.qBall'_subset_image_ball huq)
  have huR := c.morseNorm_le_R_of_sq_lt (c.symm_sq_lt_of_mem_qBall' huq)
  rcases le_or_gt c.hi₁ (f (k.Φ u z)) with h | h
  · refine k.RqPos_subset_Ccyc (k.mem_RqPos_of_symm huq ⟨huσ.le, ?_, hν, hQ⟩)
    rw [← c.hi₁_le_iff huR, hχu]
    exact h
  · have hζ : ‖c.ζ (k.Φ u z)‖ ≤ k.δ' := by
      have := (c.norm_ζ_le_iff_Qq_le k (c.symm_sq_lt_of_mem_qBall' huq)
        (by rw [hχu]; exact huT.1)).2 hQ
      rwa [hχu] at this
    refine k.Tmid_subset_Ccyc ⟨k.mem_Sσ_iff.2 ⟨huT, ⟨?_, ?_⟩, hζ⟩, hulo'.le, h.le⟩
    · linarith [(c₁_sub_half_lt_lo₂ (c := c))]
    · linarith [c.hi₁_mem_levels]

/-- Local invariance at a point of the upper region of `q` off the stable disc. -/
theorem local_RqPos (hk : k.Good) {z : M} (hz : z ∈ k.RqPos) (hF : z ∉ k.Fc) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.Φ u z ∈ k.Ccyc := by
  have hzq := k.RqPos_subset_qBall' hk hz
  have hu : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm z) := by
    by_contra h
    exact hF (Or.inr ⟨hz, c.mem_FqMid_of hzq (not_lt.1 h)⟩)
  rcases (k.hi₁_le_f_of_mem_Rq hk (k.RqPos_subset_Rq hz)).lt_or_eq with h | h
  · exact k.local_RqPos_open hk hz hu h
  · exact k.local_RqPos_hi₁ hk hz hu h.symm

/-- **Local forward invariance of the cycle region off its faces.** -/
theorem local_Ccyc (hk : k.Good) {z : M} (hz : z ∈ k.Ccyc) (hF : z ∉ k.Fc) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.Φ u z ∈ k.Ccyc := by
  rcases hz with (h | h) | h
  · exact k.local_Ann hk h hF
  · rcases h.2.1.eq_or_lt with hlo | hlo
    · exact k.local_Ann hk (c.mem_Ann_of_mem_Tmid_lo₂ k hk h hlo.symm) hF
    rcases h.2.2.eq_or_lt with hhi | hhi
    · exact k.local_RqPos hk (c.mem_RqPos_of_mem_Tmid_hi₁ k hk h hhi) hF
    exact k.local_Tmid_open h hlo hhi
  · exact k.local_RqPos hk h hF

/-- **The cycle region is forward invariant until a face is hit.** -/
theorem Φ_mem_Ccyc_until (hk : k.Good) {x : M} (hx : x ∈ k.Ccyc) {t : ℝ}
    (hF : ∀ s ∈ Icc 0 t, k.Φ s x ∉ k.Fc) : ∀ s ∈ Icc 0 t, k.Φ s x ∈ k.Ccyc := by
  have hQ : IsClosed {s : ℝ | k.Φ s x ∈ k.Ccyc} :=
    (k.isCompact_Ccyc hk).isClosed.preimage (k.continuous_Φ_curve x)
  refine Icc_subset_of_isClosed_of_step hQ (by simp [hx]) fun s hs hIcc => ?_
  have hsC : k.Φ s x ∈ k.Ccyc := hIcc (right_mem_Icc.2 hs.1)
  obtain ⟨ε, hε, hεC⟩ := k.local_Ccyc hk hsC (hF s (Ico_subset_Icc_self hs))
  refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (s + ε) t, lt_min (by linarith) hs.2,
    fun s' hs' => ?_⟩
  have hs'ε : s' ≤ s + ε := hs'.2.trans (min_le_left _ _)
  show k.Φ s' x ∈ k.Ccyc
  have := hεC (s' - s) ⟨by linarith [hs'.1], by linarith⟩
  rwa [k.Φ_Φ, add_sub_cancel] at this

/-- **First hit of a face of the cycle region.** -/
theorem exists_hit_Fc (hk : k.Good) {x : M} (hx : x ∈ k.Ccyc) :
    ∃ t, 0 ≤ t ∧ k.Φ t x ∈ k.Fc ∧ ∀ s ∈ Icc 0 t, k.Φ s x ∈ k.Ccyc := by
  obtain ⟨t, ht, hexit⟩ := k.exists_exit_Ccyc hk x hx
  obtain ⟨t₁, ht₁, -, ht₁F, hall, -⟩ := k.exists_first_hit_face (k.isCompact_Ccyc hk).isClosed
    (k.isClosed_Fc hk) hx (fun t hF => k.Φ_mem_Ccyc_until hk hx hF) ht hexit
  exact ⟨t₁, ht₁, ht₁F, hall⟩


/-! ### The assembly: every point of the strip descends below `a'` -/

/-- A point of the cycle region on the stable disc of `q` descends below `a'`. -/
theorem exists_f_le_a'_of_mem_RqPos_FqMid (hk : k.Good) {z : M} (hz : z ∈ k.RqPos)
    (hF : z ∈ c.FqMid) : ∃ T, 0 ≤ T ∧ f (k.Φ T z) ≤ a' := by
  have hu : c.σ * uq c.d.hk c.hkq (c.d.χ.symm z) = 0 :=
    le_antisymm (c.σ_uq_le_of_mem_FqMid hF) (k.symm_mem_RegQPos_of_mem_RqPos hk hz).1
  exact k.exists_f_le_a'_of_mem_RqNeg hk (k.mem_RqNeg_of_mem_RqPos hk hz hu)

/-- **From `Wp2 ∩ Tmid` at the level `lo₂`, the trajectory descends below `a'`**: the first face
of the cycle region hit is the stable disc of `q` (the inner sphere is excluded by the
monotonicity of the transported angle: `L ≤ b₀` there, and then the radius increases). -/
theorem exists_f_le_a'_of_mem_Wp2_Tmid (hk : k.Good) {x : M} (hx2 : x ∈ k.Wp2)
    (hxT : x ∈ k.Tmid) (hf : f x = c.lo₂) : ∃ T, 0 ≤ T ∧ f (k.Φ T x) ≤ a' := by
  obtain ⟨t, ht, htF, hall⟩ := k.exists_hit_Fc hk (k.Tmid_subset_Ccyc hxT)
  rcases htF with hS | ⟨hR, hM⟩
  · -- the inner sphere: excluded
    exfalso
    obtain ⟨y₀, hy₀, hy₀t⟩ := hS
    have hy₀' : morseNorm n y₀ = c.ρs := hy₀
    have hy₀sq : morseNorm n y₀ ^ 2 < 3 * c.ε := by rw [hy₀']; exact ρs_sq_lt (c := c)
    have htp : k.Φ t x ∈ c.pBall' := ⟨y₀, hy₀sq, hy₀t⟩
    have hsymm : c.e.χ.symm (k.Φ t x) = y₀ := by
      rw [← hy₀t, c.chart_p_symm_eq' hy₀sq]
    -- `L ≤ b₀` at the hit
    have hxp := c.Wball_subset_pBall' (k.Wp2_subset_Wball hx2)
    obtain ⟨-, -, hB⟩ := (k.mem_Wp2_iff (c.pBall'_subset_image_ball hxp)).1 hx2
    have hmono := k.antitoneOn_L_Φ hk hall
    have hL : c.L (k.Φ t x) ≤ c.L (k.Φ 0 x) := hmono (left_mem_Icc.2 ht) (right_mem_Icc.2 ht) ht
    rw [k.Φ_zero, c.L_of_mem_pBall' hxp, c.L_of_mem_pBall' htp, hsymm] at hL
    have hBy₀ : Bm c.e₁ y₀ ≤ k.b₀ := hL.trans hB
    -- the radius strictly increases at the hit
    have hdot := k.dot_Vp_pos_of_inner_sphere hy₀' hBy₀
    have hd := k.hasDerivAt_morseNormSq_Φ_p htp
    rw [hsymm] at hd
    have hev := eventually_lt_left_of_hasDerivAt_pos (by linarith : 0 < 2 * dot y₀ (k.Vp y₀)) hd
    -- `t > 0`
    have htpos : 0 < t := by
      rcases ht.eq_or_lt with h | h
      · exfalso
        have := hk.Sσ_lo₂_radius hxT.1 hf
        rw [← h, k.Φ_zero] at hsymm
        rw [hsymm, hy₀'] at this
        exact c.ρs_lt_ρB.ne this.2
      · exact h
    -- near the hit, the level is below `lo₂` and the point is in the ball of `p`
    have hflt : f (k.Φ t x) < c.lo₂ := by
      rw [c.f_eq_of_mem_pBall' htp, hsymm, hy₀']
      have := c.ρB_sq_eq
      have := pow_lt_pow_left₀ c.ρs_lt_ρB c.ρs_pos.le two_ne_zero
      linarith
    have hO : k.Φ t x ∈ c.pBall' ∩ {w | f w < c.lo₂} := ⟨htp, hflt⟩
    have hmem : ∀ᶠ s in 𝓝[<] t, k.Φ s x ∈ c.pBall' ∩ {w | f w < c.lo₂} :=
      nhdsWithin_le_nhds ((k.continuous_Φ_curve x).continuousAt.preimage_mem_nhds
        ((c.isOpen_pBall'.inter (isOpen_lt c.hfs.continuous continuous_const)).mem_nhds hO))
    obtain ⟨s, ⟨hlt, hsp, hsf⟩, hs⟩ := ((hev.and hmem).and (Ioo_mem_nhdsLT htpos)).exists
    have hsC := hall s ⟨hs.1.le, hs.2.le⟩
    have hsf' : f (k.Φ s x) < c.lo₂ := hsf
    rw [hsymm, hy₀'] at hlt
    rcases hsC with (hA | hT) | hR
    · have := (c.symm_mem_of_mem_Ann hA).1
      have h2 := pow_le_pow_left₀ c.ρs_pos.le this 2
      linarith
    · linarith [hT.2.1]
    · linarith [k.f_ge_lo₂_of_mem_RqPos hk hR]
  · obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_RqPos_FqMid hk hR hM
    exact ⟨t + T, by linarith, by rw [k.Φ_add]; exact hfT⟩

/-- **From the ball region of `p`, the trajectory descends below `a'`.** -/
theorem exists_f_le_a'_of_mem_Wball (hk : k.Good) {x : M} (hx : x ∈ c.Wball) :
    ∃ T, 0 ≤ T ∧ f (k.Φ T x) ≤ a' := by
  obtain ⟨t, ht, hW2, hT, hf⟩ := k.exists_reach_Wp2_Tmid hk hx
  obtain ⟨T, hT', hfT⟩ := k.exists_f_le_a'_of_mem_Wp2_Tmid hk hW2 hT hf
  exact ⟨t + T, by linarith, by rw [k.Φ_add]; exact hfT⟩

/-- **From the cycle region, the trajectory descends below `a'`.** -/
theorem exists_f_le_a'_of_mem_Ccyc (hk : k.Good) {x : M} (hx : x ∈ k.Ccyc) :
    ∃ T, 0 ≤ T ∧ f (k.Φ T x) ≤ a' := by
  obtain ⟨t, ht, htF, -⟩ := k.exists_hit_Fc hk hx
  rcases htF with hS | ⟨hR, hM⟩
  · obtain ⟨y₀, hy₀, hy₀t⟩ := hS
    have hy₀' : morseNorm n y₀ = c.ρs := hy₀
    have hy₀B : morseNorm n y₀ ≤ c.ρB := by rw [hy₀']; exact c.ρs_lt_ρB.le
    have hW : k.Φ t x ∈ c.Wball := ⟨y₀, hy₀B, hy₀t⟩
    obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_Wball hk hW
    exact ⟨t + T, by linarith, by rw [k.Φ_add]; exact hfT⟩
  · obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_RqPos_FqMid hk hR hM
    exact ⟨t + T, by linarith, by rw [k.Φ_add]; exact hfT⟩

theorem hi₁_mem_Icc : c.hi₁ ∈ Icc a' b' := by
  have h1 := c.a'_lt_lo₂
  have h2 := c.lo₂_lt_hi₁
  have h3 := c.c₂_add_η_lt_b'
  have h4 := c.η_pos
  unfold hi₁ at *
  exact ⟨by linarith, by linarith⟩

/-- **From the region of `q`, the trajectory descends below `a'`**: through the lower face, or
through the level `hi₁` into the middle band, or (with a large transverse coordinate) off `K`
along the original field until the ball region of `p` or the middle band is entered. -/
theorem exists_f_le_a'_of_mem_Rq (hk : k.Good) {x : M} (hx : x ∈ k.Rq) :
    ∃ T, 0 ≤ T ∧ f (k.Φ T x) ≤ a' := by
  obtain ⟨t, ht, hall, -, hface⟩ := k.exists_exit_Rq_face hk hx
  have htR := hall t (right_mem_Icc.2 ht)
  rcases hface with hu | hf
  · obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_Rq_face hk htR hu
    exact ⟨t + T, by linarith, by rw [k.Φ_add]; exact hfT⟩
  -- the level `hi₁`
  set z := k.Φ t x with hzdef
  suffices h : ∃ T, 0 ≤ T ∧ f (k.Φ T z) ≤ a' by
    obtain ⟨T, hT, hfT⟩ := h
    exact ⟨t + T, by linarith, by rw [k.Φ_add]; exact hfT⟩
  have hzq := k.Rq_subset_qBall' hk htR
  have hχ : c.d.χ (c.d.χ.symm z) = z := c.d.symm_image_eq (c.qBall'_subset_image_ball hzq)
  have hy := k.symm_mem_RegQ_of_mem_Rq hk htR
  obtain ⟨huB, hT⟩ := k.hi₁_face hk hy (by rw [hχ]; exact hf)
  rw [hχ] at hT
  have hsq := c.symm_sq_lt_of_mem_qBall' hzq
  by_cases hQ : c.Qq (c.d.χ.symm z) ≤ k.Q'
  · -- small transverse coordinate: in the middle band
    have hζ : ‖c.ζ z‖ ≤ k.δ' := by
      have := (c.norm_ζ_le_iff_Qq_le k hsq (by rw [hχ]; exact hT.1)).2 hQ
      rwa [hχ] at this
    have hzT : z ∈ k.Tmid :=
      ⟨k.mem_Sσ_iff.2 ⟨hT, ⟨by rw [hf]; linarith [c₁_sub_half_lt_lo₂ (c := c), c.lo₂_lt_hi₁],
        by rw [hf]; exact c.hi₁_mem_levels⟩, hζ⟩, by rw [hf]; exact c.lo₂_lt_hi₁.le, hf.le⟩
    exact k.exists_f_le_a'_of_mem_Ccyc hk (k.Tmid_subset_Ccyc hzT)
  -- large transverse coordinate: `z ∉ K`
  push Not at hQ
  have hζ : k.δ' < ‖c.ζ z‖ := by
    by_contra h
    push Not at h
    have := (c.norm_ζ_le_iff_Qq_le k hsq (by rw [hχ]; exact hT.1)).1 (by rw [hχ]; exact h)
    linarith
  have hv : posPart c.d.hk (c.d.χ.symm z) ≠ 0 := by
    intro h
    have : c.Qq (c.d.χ.symm z) = 0 := by unfold Qq; rw [h, norm_zero]; ring
    linarith [k.Q'_pos]
  have hzK : z ∉ k.K := by
    rintro ((hKp | hKq) | hS)
    · exact (c.D.disjoint p c.hp q c.hq c.p_ne_q).notMem_of_mem_left
        (image_mono k.Kp_subset_ball hKp) (c.qBall'_subset_image_ball hzq)
    · obtain ⟨y', hy', hy'z⟩ := hKq
      have hy'eq : c.d.χ.symm z = y' := by
        rw [← hy'z, c.d.χ.left_inv (c.d.hball (k.Kq_subset_ball hy'))]
      have h1 := hy'.1
      rw [← hy'eq] at h1
      have h2 : uq c.d.hk c.hkq (c.d.χ.symm z) ^ 2 =
          c.uB ^ 2 + ‖posPart c.d.hk (c.d.χ.symm z)‖ ^ 2 := by
        have := c.f_chart_q (c.morseNorm_le_R_of_sq_lt hsq)
        rw [hχ, hf] at this
        rw [c.uB_sq_eq]
        linarith
      have h3 : 0 < ‖posPart c.d.hk (c.d.χ.symm z)‖ ^ 2 := by positivity
      linarith
    · exact absurd (k.norm_ζ_le_of_mem_Sσ hS) (not_le.2 hζ)
  -- the off-`K` phase from `z`
  obtain ⟨t₁, ht₁, hhit, hbefore⟩ := k.exists_hit_K_or_bottom (x := z)
    (by rw [hf]; exact hi₁_mem_Icc (c := c))
  rcases hhit with hK | hle
  · -- the trajectory is the original flow up to `t₁`; the level at `t₁` is below `hi₁`
    have ht₁pos : 0 < t₁ := by
      rcases ht₁.eq_or_lt with h | h
      · exfalso; rw [← h, k.Φ_zero] at hK; exact hzK hK
      · exact h
    have hflow := k.flow_eq_Φ_of_avoid (fun s hs => (hbefore s hs).1)
    have hd : HasDerivAt (fun s => f (c.D.flow s z)) (dfV I f c.D.V (c.D.flow 0 z)) 0 :=
      hasDerivAt_df_comp_integralCurve f c.hfs c.D.V (c.D.isMIntegralCurve_flow z) 0
    have hfz : f z ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η) := by
      rw [hf]
      have h1 := c.lo₂_lt_hi₁
      have h2 := c.η_pos
      have h3 := c₁_sub_half_lt_lo₂ (c := c)
      unfold hi₁ at *
      exact ⟨by linarith, by linarith⟩
    rw [c.D.flow_zero, c.dfV_V_eq_neg_one_of_mem_tube hfz] at hd
    have hev := eventually_lt_of_hasDerivAt_neg (by norm_num : (-1 : ℝ) < 0) hd
    obtain ⟨s₁, hlt, hs₁⟩ := (hev.and (Ioc_mem_nhdsGT ht₁pos)).exists
    rw [c.D.flow_zero] at hlt
    have hfw : f (k.Φ t₁ z) < c.hi₁ := by
      rw [← hflow t₁ (right_mem_Icc.2 ht₁)]
      have := f_flow_le c.hfs (D := c.D) (c.D.flow s₁ z) (t := t₁ - s₁) (by linarith [hs₁.2])
      rw [flow_flow, add_sub_cancel] at this
      linarith
    rcases k.mem_K_cases hk hK with hW | hT | hR
    · obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_Wball hk hW
      exact ⟨t₁ + T, by linarith, by rw [k.Φ_add]; exact hfT⟩
    · obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_Ccyc hk (k.Tmid_subset_Ccyc hT)
      exact ⟨t₁ + T, by linarith, by rw [k.Φ_add]; exact hfT⟩
    · exact absurd (k.hi₁_le_f_of_mem_Rq hk hR) (not_le.2 hfw)
  · exact ⟨t₁, ht₁, hle⟩

/-- **From `K`, the trajectory descends below `a'`.** -/
theorem exists_f_le_a'_of_mem_K (hk : k.Good) {x : M} (hx : x ∈ k.K) :
    ∃ T, 0 ≤ T ∧ f (k.Φ T x) ≤ a' := by
  rcases k.mem_K_cases hk hx with hW | hT | hR
  · exact k.exists_f_le_a'_of_mem_Wball hk hW
  · exact k.exists_f_le_a'_of_mem_Ccyc hk (k.Tmid_subset_Ccyc hT)
  · exact k.exists_f_le_a'_of_mem_Rq hk hR

/-- **Every point of the strip descends below `a'` along the modified flow.** -/
theorem exists_f_Φ_le_a' (hk : k.Good) {x : M} (hx : f x ∈ Icc a' b') :
    ∃ T, 0 ≤ T ∧ f (k.Φ T x) ≤ a' := by
  obtain ⟨t, ht, hhit, -⟩ := k.exists_hit_K_or_bottom hx
  rcases hhit with hK | hle
  · obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_K hk hK
    exact ⟨t + T, by linarith, by rw [k.Φ_add]; exact hfT⟩
  · exact ⟨t, ht, hle⟩

/-- **`reaches_bottom`**: every point of the strip reaches the level `a'` along the modified flow
at a first time, staying strictly above `a'` before. -/
theorem reaches_bottom (hk : k.Good) {x : M} (hx : f x ∈ Icc a' b') :
    ∃ t, 0 ≤ t ∧ f (k.Φ t x) = a' ∧ ∀ s ∈ Ico 0 t, a' < f (k.Φ s x) := by
  obtain ⟨T, hT, hfT⟩ := k.exists_f_Φ_le_a' hk hx
  have hcl : IsClosed (f ⁻¹' Iic a') := isClosed_Iic.preimage c.hfs.continuous
  obtain ⟨t, ht, htK, hmin⟩ := exists_first_time hcl (k.continuous_Φ_curve x) (t := T)
    ⟨T, ⟨hT, le_rfl⟩, hfT⟩
  have hgt : ∀ s ∈ Ico 0 t, a' < f (k.Φ s x) := fun s hs => not_le.1 (hmin s hs)
  refine ⟨t, ht.1, le_antisymm htK ?_, hgt⟩
  rcases ht.1.eq_or_lt with h | h
  · rw [← h, k.Φ_zero]; exact hx.1
  · have := k.mem_of_mem_Ico (A := f ⁻¹' Ici a') (isClosed_Ici.preimage c.hfs.continuous) h
      (fun s hs => (hgt s hs).le)
    exact this

end CancelConsts

end CancelData

end GradientLikeStrip

end

end PoincareHighDim
