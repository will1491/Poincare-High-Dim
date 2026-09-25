import Submission.Morse.CancelPair
import Submission.Morse.NegDual
import Submission.Morse.DistinctSelfIndexing

/-!
# Elimination of critical points of extremal index

Milnor, *Lectures on the h-cobordism theorem*, Theorem 8.1.

* `exists_no_extremal_index` (index `0` and `n`): if every component of the strip meets both
  ends (here: the strip is connected and both ends are nonempty), the critical points of index
  `0` can be cancelled against index-`1` points (Milnor's First Cancellation Theorem 5.4 applied
  to a pair whose spheres meet in one point), and dually for index `n`.
* `exists_index_in_middle` (index `1` and `n - 1`): if the strip and its ends are simply
  connected and `n ≥ 5`, index-`1` points are traded for index-`3` points (insertion of an
  auxiliary cancelling pair of index `2, 3` followed by a cancellation), and dually for index
  `n - 1`.

## The proof of `exists_no_extremal_index`

One index-`0` point is removed by `exists_cancel_index_zero_step`: the critical values are made
distinct keeping self-indexing (`exists_distinct_selfIndexing`), a gradient-like field in
general position for all pairs of index-`1` points is chosen (`exists_gradientLike_allPairs`),
Milnor's graph argument produces a good pair `(p, q)` — an index-`1` point `q` exactly one of
whose arms descends into the basin of the index-`0` point `p` (`exists_bridge`) — the pair is
isolated in a regular substrip by rearrangement (`exists_isolated_pair`), and the First
Cancellation Theorem for index `0` (`exists_cancel_pair_index_zero`, proved in the modules
`CancelSetup` … `CancelIndexZero`, through `exists_cancel_pair_strip`) removes it.  The other critical points keep their values and
indices, so self-indexing survives and the number of index-`0` points drops by one;
`exists_no_index_zero` is the induction on that number.  The index-`n` points are removed by
the same statement applied to `-f` on `[-b, -a]` (`Submission/Morse/NegDual.lean`: index `k` of
`f` is index `n - k` of `-f`), which creates no new critical points and keeps the indices, so
the result has no critical point of index `0` or `n`.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **One cancellation step.**  If `f` has an index-`0` critical point in the open strip, it can
be modified within the strip, keeping self-indexing, so that some index-`0` critical point of
`f` is no longer critical, while every critical point of the result is a critical point of `f`
of the same index. -/
theorem exists_cancel_index_zero_step (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) (hsi : IsSelfIndexing I f a b)
    (hconn : ConnectedSpace (f ⁻¹' Icc a b)) (ha : (f ⁻¹' {a}).Nonempty)
    {p₀ : M} (hp₀ : f p₀ ∈ Ioo a b ∧ IsCriticalPt I f p₀ ∧ morseIndex I f p₀ = 0) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ IsSelfIndexing I g a b ∧
      (∀ x, g x ∈ Ioo a b → IsCriticalPt I g x →
        IsCriticalPt I f x ∧ morseIndex I g x = morseIndex I f x) ∧
      ∃ p, (f p ∈ Ioo a b ∧ IsCriticalPt I f p ∧ morseIndex I f p = 0) ∧
        ¬ IsCriticalPt I g p := by
  classical
  -- Step 1: distinct critical values, keeping self-indexing
  obtain ⟨g₁, hmod₁, hf₁, hsi₁, hcrit₁, hidx₁, hinj₁⟩ := exists_distinct_selfIndexing I hf hsi
  have hIoo₁ : ∀ x, g₁ x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₁.preimage_Ioo x
  -- the critical set of `g₁`
  set crit : Finset M := (hf₁.finite_critical.subset fun x hx =>
    ⟨Ioo_subset_Icc_self hx.1, hx.2⟩ :
      {x | g₁ x ∈ Ioo a b ∧ IsCriticalPt I g₁ x}.Finite).toFinset with hcritdef
  have hcrit : ∀ x, x ∈ crit ↔ g₁ x ∈ Ioo a b ∧ IsCriticalPt I g₁ x := fun x => by
    rw [hcritdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  -- Step 2: the chart bound `R₀` (the critical values are `16 R₀²`-separated)
  obtain ⟨ρ₁, hρ₁, hρ₁T⟩ := exists_pos_le_forall_finset
    ((crit ×ˢ crit).filter fun x => g₁ x.1 < g₁ x.2) (fun x => g₁ x.2 - g₁ x.1)
    fun x hx => sub_pos.2 (Finset.mem_filter.1 hx).2
  obtain ⟨ρ₂, hρ₂, hρ₂T⟩ := exists_pos_le_forall_finset crit
    (fun r => min (g₁ r - a) (b - g₁ r))
    fun r hr => lt_min (sub_pos.2 ((hcrit r).1 hr).1.1) (sub_pos.2 ((hcrit r).1 hr).1.2)
  have hmin : 0 < min ρ₁ ρ₂ := lt_min hρ₁ hρ₂
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = Real.sqrt (min ρ₁ ρ₂ / 32) := ⟨_, rfl⟩
  have hR₀ : 0 < R₀ := by rw [hR₀def]; exact Real.sqrt_pos.2 (by positivity)
  have hR₀sq : 16 * R₀ ^ 2 = min ρ₁ ρ₂ / 2 := by
    rw [hR₀def, Real.sq_sqrt (by positivity)]
    ring
  have hgap : ∀ r ∈ crit, ∀ s ∈ crit, g₁ r < g₁ s → g₁ r + 16 * R₀ ^ 2 < g₁ s := by
    intro r hr s hs hlt
    have := hρ₁T (r, s) (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hr, hs⟩, hlt⟩)
    simp only at this
    rw [hR₀sq]
    linarith [min_le_left ρ₁ ρ₂]
  have hab : ∀ r ∈ crit, a + 16 * R₀ ^ 2 < g₁ r ∧ g₁ r + 16 * R₀ ^ 2 < b := by
    intro r hr
    have := hρ₂T r hr
    rw [hR₀sq]
    constructor <;> linarith [min_le_right ρ₁ ρ₂, min_le_left (g₁ r - a) (b - g₁ r),
      min_le_right (g₁ r - a) (b - g₁ r)]
  -- Step 3: general position between the index-`1` points
  obtain ⟨D, ε, hε, r', hr', hr'ε, hD, hE2, hE3⟩ :=
    GradientLikeStrip.exists_gradientLike_allPairs hf₁ hsi₁ hinj₁ crit hcrit hR₀
  -- Step 4: a good pair
  have hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2 := fun p hp =>
    ⟨(hD p hp).2.1, by linarith [(hD p hp).2.2.1]⟩
  have hidx := GradientLikeStrip.k_lt_imp_f_lt_of_selfIndexing D hsi₁ hcrit
  have hinjc : InjOn g₁ (crit : Set M) := fun x hx y hy h =>
    hinj₁ ((hcrit x).1 (Finset.mem_coe.1 hx)) ((hcrit y).1 (Finset.mem_coe.1 hy)) h
  have hconn₁ : ConnectedSpace (g₁ ⁻¹' Icc a b) :=
    hmod₁.connectedSpace_preimage_Icc_iff.2 hconn
  have ha₁ : (g₁ ⁻¹' {a}).Nonempty := hmod₁.nonempty_preimage_singleton_left_iff.2 ha
  have hp₀c : p₀ ∈ crit := (hcrit p₀).2 ⟨(hIoo₁ p₀).2 hp₀.1, (hcrit₁ p₀ hp₀.1).2 hp₀.2.1⟩
  have hk₀ : (D.chart p₀ hp₀c).k = 0 := by
    rw [← (D.chart p₀ hp₀c).hkidx, hidx₁ p₀ hp₀.1 hp₀.2.1]
    exact hp₀.2.2
  obtain ⟨p, q, hp, hq, hgood⟩ := GradientLikeStrip.exists_bridge (D := D) hf₁.smooth hε hεr
    hr' hidx hE3 hinjc hconn₁ ha₁ hp₀c hk₀
  -- Step 5: isolation of the pair in a regular substrip
  obtain ⟨g₂, hmod₂, hf₂, hsi₂, hcrit₂, hidx₂, -, a', b', haa', ha'p, hpq, hqb', hb'b, hreg,
    hcrit', D', ε', hε', -, hgood', hD', h2ε', hlev⟩ :=
    GradientLikeStrip.exists_isolated_pair hf₁ hsi₁ hinj₁ hcrit D hε hr'ε hD hE2 hE3 hgap hab
      hp hq hgood
  -- Step 6: cancellation
  have hf₂' : MorseStrip I g₂ a' b' :=
    hf₂.substrip haa'.le (ha'p.trans (hpq.trans hqb')) hb'b.le hreg
  obtain ⟨g₃, hmod₃, hmod₃', hf₃, hoff₃, hno₃⟩ :=
    GradientLikeStrip.exists_cancel_pair_strip hf₂ haa'.le hb'b.le hreg hf₂' D' hcrit'
      (Finset.mem_insert_self p {q}) (Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
      hε' hgood' hD' h2ε' hlev
  -- assembly
  have hIoo₂ : ∀ x, g₂ x ∈ Ioo a b ↔ g₁ x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₂.preimage_Ioo x
  have hIoo₃ : ∀ x, g₃ x ∈ Ioo a b ↔ g₂ x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₃'.preimage_Ioo x
  have hout : ∀ x, IsCriticalPt I g₃ x → g₂ x ∉ Ioo a' b' := fun x hx h =>
    hno₃ x (hmod₃.mapsTo h) hx
  have hsi₃ : IsSelfIndexing I g₃ a b := by
    intro x y hx hy hcx hcy hlt
    obtain ⟨hgx, hcx', hix⟩ := hoff₃ x (hout x hcx)
    obtain ⟨hgy, hcy', hiy⟩ := hoff₃ y (hout y hcy)
    rw [hgx, hgy]
    rw [hix (hcx'.1 hcx), hiy (hcy'.1 hcy)] at hlt
    exact hsi₂ x y ((hIoo₃ x).1 hx) ((hIoo₃ y).1 hy) (hcx'.1 hcx) (hcy'.1 hcy) hlt
  refine ⟨g₃, hmod₁.trans (hmod₂.trans hmod₃'), hf₃, hsi₃, fun x hx hcx => ?_, p, ?_, ?_⟩
  · obtain ⟨-, hcx', hix⟩ := hoff₃ x (hout x hcx)
    have hc₂ : IsCriticalPt I g₂ x := hcx'.1 hcx
    have hc₁ : IsCriticalPt I g₁ x := (hcrit₂ x).1 hc₂
    have hfx : f x ∈ Ioo a b := (hIoo₁ x).1 ((hIoo₂ x).1 ((hIoo₃ x).1 hx))
    have hcf : IsCriticalPt I f x := (hcrit₁ x hfx).1 hc₁
    exact ⟨hcf, by rw [hix hc₂, hidx₂ x hc₁, hidx₁ x hfx hcf]⟩
  · have hp₁ := (hcrit p).1 hp
    have hfp : f p ∈ Ioo a b := (hIoo₁ p).1 hp₁.1
    have hcf : IsCriticalPt I f p := (hcrit₁ p hfp).1 hp₁.2
    refine ⟨hfp, hcf, ?_⟩
    rw [← hidx₁ p hfp hcf, (D.chart p hp).hkidx]
    exact hgood.1
  · exact fun hc => hno₃ p (hmod₃.mapsTo ⟨ha'p, hpq.trans hqb'⟩) hc

/-- **Elimination of index `0`** (Milnor, Theorem 8.1, index 0): induction on the number of
index-`0` critical points, one being cancelled at each step by `exists_cancel_index_zero_step`.
Every critical point of the result is a critical point of `f` with the same index. -/
theorem exists_no_index_zero (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) (hsi : IsSelfIndexing I f a b)
    (hconn : ConnectedSpace (f ⁻¹' Icc a b)) (ha : (f ⁻¹' {a}).Nonempty) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ IsSelfIndexing I g a b ∧
      (∀ x, g x ∈ Ioo a b → IsCriticalPt I g x → 0 < morseIndex I g x) ∧
      ∀ x, g x ∈ Ioo a b → IsCriticalPt I g x →
        IsCriticalPt I f x ∧ morseIndex I g x = morseIndex I f x := by
  -- the case without index-`0` points
  have hbase : ∀ f : M → ℝ, MorseStrip I f a b → IsSelfIndexing I f a b →
      ¬ {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x ∧ morseIndex I f x = 0}.Nonempty →
      ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ IsSelfIndexing I g a b ∧
        (∀ x, g x ∈ Ioo a b → IsCriticalPt I g x → 0 < morseIndex I g x) ∧
        ∀ x, g x ∈ Ioo a b → IsCriticalPt I g x →
          IsCriticalPt I f x ∧ morseIndex I g x = morseIndex I f x := by
    intro f hf hsi hne
    refine ⟨f, ModifiedWithin.refl f a b, hf, hsi, fun x hx hc => ?_, fun x _ hc => ⟨hc, rfl⟩⟩
    by_contra h0
    exact hne ⟨x, hx, hc, by omega⟩
  suffices key : ∀ N : ℕ, ∀ f : M → ℝ, MorseStrip I f a b → IsSelfIndexing I f a b →
      ConnectedSpace (f ⁻¹' Icc a b) → (f ⁻¹' {a}).Nonempty →
      {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x ∧ morseIndex I f x = 0}.ncard ≤ N →
      ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ IsSelfIndexing I g a b ∧
        (∀ x, g x ∈ Ioo a b → IsCriticalPt I g x → 0 < morseIndex I g x) ∧
        ∀ x, g x ∈ Ioo a b → IsCriticalPt I g x →
          IsCriticalPt I f x ∧ morseIndex I g x = morseIndex I f x from
    key _ f hf hsi hconn ha le_rfl
  intro N
  induction N with
  | zero =>
    intro f hf hsi _ _ hN
    have hfin : {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x ∧ morseIndex I f x = 0}.Finite :=
      hf.finite_critical.subset fun x hx => ⟨Ioo_subset_Icc_self hx.1, hx.2.1⟩
    refine hbase f hf hsi fun hne => ?_
    have := (Set.ncard_pos hfin).2 hne
    omega
  | succ N ih =>
    intro f hf hsi hconn ha hN
    have hfin : {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x ∧ morseIndex I f x = 0}.Finite :=
      hf.finite_critical.subset fun x hx => ⟨Ioo_subset_Icc_self hx.1, hx.2.1⟩
    by_cases hne : {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x ∧ morseIndex I f x = 0}.Nonempty
    · obtain ⟨p₀, hp₀⟩ := hne
      obtain ⟨g, hmod, hg, hsig, hcritg, p, hpZ, hpg⟩ :=
        exists_cancel_index_zero_step I hf hsi hconn ha hp₀
      have hIoo : ∀ x, g x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
        Set.ext_iff.1 hmod.preimage_Ioo x
      have hsub : {x | g x ∈ Ioo a b ∧ IsCriticalPt I g x ∧ morseIndex I g x = 0} ⊂
          {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x ∧ morseIndex I f x = 0} := by
        refine ⟨fun x hx => ⟨(hIoo x).1 hx.1, (hcritg x hx.1 hx.2.1).1, ?_⟩,
          fun h => hpg (h hpZ).2.1⟩
        rw [← (hcritg x hx.1 hx.2.1).2]
        exact hx.2.2
      have hlt := Set.ncard_lt_ncard hsub hfin
      obtain ⟨g', hmod', hg', hsig', hpos', hcrit'⟩ := ih g hg hsig
        (hmod.connectedSpace_preimage_Icc_iff.2 hconn)
        (hmod.nonempty_preimage_singleton_left_iff.2 ha) (by omega)
      refine ⟨g', hmod.trans hmod', hg', hsig', hpos', fun x hx hc => ?_⟩
      obtain ⟨hcg, hig⟩ := hcrit' x hx hc
      have hgx : g x ∈ Ioo a b := (Set.ext_iff.1 hmod'.preimage_Ioo x).1 hx
      obtain ⟨hcf, hif⟩ := hcritg x hgx hcg
      exact ⟨hcf, hig.trans hif⟩
    · exact hbase f hf hsi hne

/-- **Elimination of index `0` and `n`** (Milnor, Theorem 8.1, index 0, and its dual). -/
theorem exists_no_extremal_index (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) (hsi : IsSelfIndexing I f a b)
    (hconn : ConnectedSpace (f ⁻¹' Icc a b))
    (ha : (f ⁻¹' {a}).Nonempty) (hb : (f ⁻¹' {b}).Nonempty) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ IsSelfIndexing I g a b ∧
      ∀ x, g x ∈ Ioo a b → IsCriticalPt I g x → 0 < morseIndex I g x ∧ morseIndex I g x < n := by
  -- index `0`
  obtain ⟨g₁, hmod₁, hf₁, hsi₁, hpos₁, hcrit₁⟩ := exists_no_index_zero I hf hsi hconn ha
  have hb₁ : (g₁ ⁻¹' {b}).Nonempty := hmod₁.nonempty_preimage_singleton_right_iff.2 hb
  have hconn₁ : ConnectedSpace (g₁ ⁻¹' Icc a b) :=
    hmod₁.connectedSpace_preimage_Icc_iff.2 hconn
  -- index `n`, as index `0` of `-g₁` on `[-b, -a]`
  obtain ⟨g₂', hmod₂', hf₂', hsi₂', hpos₂', hcrit₂'⟩ := exists_no_index_zero I hf₁.neg
    (hsi₁.neg hf₁) (NegDual.connectedSpace_neg_strip_iff.2 hconn₁)
    (NegDual.nonempty_neg_level_iff.2 hb₁)
  have hneg₂ : (fun x => -(fun x => -g₂' x) x) = g₂' := funext fun x => neg_neg _
  have hmod₂ : ModifiedWithin g₁ a b (fun x => -g₂' x) :=
    ModifiedWithin.of_neg (by rw [hneg₂]; exact hmod₂')
  have hf₂ : MorseStrip I (fun x => -g₂' x) a b := MorseStrip.of_neg (by rw [hneg₂]; exact hf₂')
  have hsi₂ : IsSelfIndexing I (fun x => -g₂' x) a b :=
    IsSelfIndexing.of_neg hf₂ (by rw [hneg₂]; exact hsi₂')
  refine ⟨fun x => -g₂' x, hmod₁.trans hmod₂, hf₂, hsi₂, fun x hx hc => ?_⟩
  have hx' : g₂' x ∈ Ioo (-b) (-a) := by
    have : -(-g₂' x) ∈ Ioo (-b) (-a) := NegDual.neg_mem_Ioo_iff.2 hx
    rwa [neg_neg] at this
  have hc' : IsCriticalPt I g₂' x := by
    have := (NegDual.isCriticalPt_neg_iff I (fun x => -g₂' x) x).2 hc
    rwa [hneg₂] at this
  have hnd' : IsNondegenerateCriticalPt I g₂' x := hf₂'.nondegenerate x hx' hc'
  have hpos := hpos₂' x hx' hc'
  obtain ⟨hc₁', hidx'⟩ := hcrit₂' x hx' hc'
  have hx₁ : g₁ x ∈ Ioo a b := by
    have : x ∈ g₂' ⁻¹' Ioo (-b) (-a) := hx'
    rw [hmod₂'.preimage_Ioo] at this
    exact NegDual.neg_mem_Ioo_iff.1 this
  have hc₁ : IsCriticalPt I g₁ x := (NegDual.isCriticalPt_neg_iff I g₁ x).1 hc₁'
  have hnd₁ : IsNondegenerateCriticalPt I g₁ x := hf₁.nondegenerate x hx₁ hc₁
  have hpos₁' := hpos₁ x hx₁ hc₁
  have h1 := NegDual.morseIndex_neg_add hnd₁
  have h2 := NegDual.morseIndex_neg_add hnd'
  omega

/-- **Elimination of index `1` and `n - 1`** (Milnor, Theorem 8.1, index 1, and its dual). -/
theorem exists_index_in_middle (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (h5 : 5 ≤ n)
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) (hsi : IsSelfIndexing I f a b)
    (hidx : ∀ x, f x ∈ Ioo a b → IsCriticalPt I f x → 0 < morseIndex I f x ∧ morseIndex I f x < n)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b))
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) (hV₁ : SimplyConnectedSpace (f ⁻¹' {b})) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ IsSelfIndexing I g a b ∧
      ∀ x, g x ∈ Ioo a b → IsCriticalPt I g x →
        2 ≤ morseIndex I g x ∧ morseIndex I g x + 2 ≤ n := by
  sorry

end PoincareHighDim
