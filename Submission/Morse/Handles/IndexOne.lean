/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Submission.Morse.Cancellation.FirstCancellation
import Submission.Morse.Rearrangement.SelfIndexing
import Submission.Morse.Handles.Partners.PartnerIsolate

/-!
# Trading critical points of index 1 for index 3 (Milnor 8.1, index 1)

Milnor, *Lectures on the h-cobordism theorem*, Theorem 8.1 (index 1) with Lemmas 8.2, 8.3, 8.4:
if the strip `W = f ⁻¹' [a, b]` is simply connected, its lower end `V₀ = f ⁻¹' {a}` is
connected, `n ≥ 5`, and `f` is a self-indexing Morse function without critical points of index
`0` or `n`, then every critical point of index `1` can be traded for one of index `3`.

* `exists_index_one_partner` (the geometric heart): for an index-`1` critical point `p`, the
  function can be modified within the strip so that two new critical points appear, `q` of
  index `2` and one of index `3`, and `p`, `q` form a cancelling pair (`IsCancellingPair`) on a
  regular substrip.  Milnor's proof: an embedded circle in the level `V_{1+}` (between the
  index-`1` and index-`2` values) meeting the right sphere of `p` once transversally and no other
  right sphere (Lemma 8.3); its translate `S₁` to the level `V_{2+}` (between the index-`2` and
  index-`3` values), which is simply connected because `W` is obtained from it by attaching cells
  of dimension `≥ 3` on both sides (`n ≥ 5`); the insertion of an auxiliary pair of index `2`
  and `3` to the right of `V_{2+}` (Lemma 8.2); an isotopy of `V_{2+}` carrying the left circle of
  the new index-`2` point to `S₁` (Lemma 8.4 with Whitney's bound `n - 1 ≥ 2·1 + 2`, and the
  isotopy extension theorem 5.8), realised by the gradient-like field (Lemma 4.7); and a
  rearrangement (Theorem 4.2) isolating `p` and `q` in a substrip.  It is proved as
  `IndexOnePartner.partner_target` in the modules `PartnerDefs` … `PartnerIsolate` (overview
  in `Submission/Morse/Handles/Partners/PartnerDefs.lean`).
* `exists_trade_index_one_step` : one index-`1` point is removed and at most one index-`3` point
  is added, keeping self-indexing (First Cancellation Theorem and re-sorting).
* `exists_no_index_one` : induction on the number of index-`1` points.

Conventions: fields descend (`df(V) ∈ [-1, 0]`), spheres are fixed-time flow images.
-/

open Set Filter

namespace PoincareHighDim

open scoped Manifold ContDiff Topology

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **The cancelling partner of an index-`1` point** (Milnor 8.1, index 1, with Lemmas 8.2–8.4):
under the hypotheses of the index-`1` elimination, the function can be modified within the strip
so that `p` and a new critical point `q` of index `2` form a cancelling pair on a regular
substrip `[a', b']`; every other critical point of the modification is an old critical point
with its old index or a new point of index `3`. -/
theorem exists_index_one_partner (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [DecidableEq M] (h5 : 5 ≤ n)
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) (hsi : IsSelfIndexing I f a b)
    (hidx : ∀ x, f x ∈ Ioo a b → IsCriticalPt I f x → 0 < morseIndex I f x ∧ morseIndex I f x < n)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b)) (hV₀ : ConnectedSpace (f ⁻¹' {a}))
    {p : M} (hp : f p ∈ Ioo a b ∧ IsCriticalPt I f p ∧ morseIndex I f p = 1) :
    ∃ f₁ : M → ℝ, ModifiedWithin f a b f₁ ∧ MorseStrip I f₁ a b ∧
      ∃ q : M, ∃ a' b' : ℝ, a < a' ∧ b' < b ∧
        (∀ x, f₁ x = a' ∨ f₁ x = b' → ¬ IsCriticalPt I f₁ x) ∧
        IsCancellingPair I f₁ a' b' p q ∧
        ∀ x, f₁ x ∈ Ioo a b → IsCriticalPt I f₁ x →
          (IsCriticalPt I f x ∧ morseIndex I f₁ x = morseIndex I f x) ∨ x = q ∨
            morseIndex I f₁ x = 3 := by
  exact IndexOnePartner.partner_target I h5 hf hsi hidx hW hV₀ hp

/-- **Trading one index-`1` point** (Milnor 8.1, index 1): under the hypotheses of the
index-`1` elimination, the critical point `p` of index `1` can be removed; the modification is a
self-indexing Morse function whose critical points are old critical points with their old index
or new points of index `3`. -/
theorem exists_trade_index_one_step (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (h5 : 5 ≤ n)
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) (hsi : IsSelfIndexing I f a b)
    (hidx : ∀ x, f x ∈ Ioo a b → IsCriticalPt I f x → 0 < morseIndex I f x ∧ morseIndex I f x < n)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b)) (hV₀ : ConnectedSpace (f ⁻¹' {a}))
    {p : M} (hp : f p ∈ Ioo a b ∧ IsCriticalPt I f p ∧ morseIndex I f p = 1) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ IsSelfIndexing I g a b ∧
      (∀ x, g x ∈ Ioo a b → IsCriticalPt I g x →
        (IsCriticalPt I f x ∧ morseIndex I g x = morseIndex I f x) ∨ morseIndex I g x = 3) ∧
      ¬ IsCriticalPt I g p := by
  classical
  obtain ⟨f₁, hmod₁, hf₁, q, a', b', ha', hb', hreg', hpair, hcrit₁⟩ :=
    exists_index_one_partner I h5 hf hsi hidx hW hV₀ hp
  obtain ⟨g₂, hmod₂', hmod₂, hg₂, hoff₂, hno₂⟩ :=
    exists_cancel_pair_strip_of_isCancellingPair I hf₁ ha'.le hb'.le hreg' hpair
  obtain ⟨g, hmod₃, hg, hsi', hcrit₃, hidx₃⟩ := exists_selfIndexing I hg₂
  have hp' : f₁ p ∈ Ioo a' b' ∧ IsCriticalPt I f₁ p := (hpair.2.1 p).1 (mem_pair_left p q)
  have hq' : f₁ q ∈ Ioo a' b' ∧ IsCriticalPt I f₁ q := (hpair.2.1 q).1 (mem_pair_right p q)
  have hpre₂ : ∀ x, g₂ x ∈ Ioo a b ↔ f₁ x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₂.preimage_Ioo x
  have hpre₃ : ∀ x, g x ∈ Ioo a b ↔ g₂ x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₃.preimage_Ioo x
  refine ⟨g, hmod₁.trans (hmod₂.trans hmod₃), hg, hsi', fun x hx hc => ?_, ?_⟩
  · have hx₂ : g₂ x ∈ Ioo a b := (hpre₃ x).1 hx
    have hc₂ : IsCriticalPt I g₂ x := (hcrit₃ x hx₂).1 hc
    have hidx₂ : morseIndex I g x = morseIndex I g₂ x := hidx₃ x hx₂ hc₂
    have hx₁ : f₁ x ∉ Ioo a' b' := fun hx₁ => hno₂ x (hmod₂'.mapsTo hx₁) hc₂
    obtain ⟨-, hcrit_iff, hidx_eq⟩ := hoff₂ x hx₁
    have hc₁ : IsCriticalPt I f₁ x := hcrit_iff.1 hc₂
    have hx₁' : f₁ x ∈ Ioo a b := (hpre₂ x).1 hx₂
    rw [hidx₂, hidx_eq hc₁]
    rcases hcrit₁ x hx₁' hc₁ with h | h | h
    · exact Or.inl h
    · rw [h] at hx₁
      exact absurd hq'.1 hx₁
    · exact Or.inr h
  · intro hc
    have hp₂ : g₂ p ∈ Ioo a' b' := hmod₂'.mapsTo hp'.1
    have hp₂b : g₂ p ∈ Ioo a b :=
      (hpre₂ p).2 ⟨ha'.trans hp'.1.1, hp'.1.2.trans hb'⟩
    exact hno₂ p hp₂ ((hcrit₃ p hp₂b).1 hc)

/-- **Elimination of index `1`** (Milnor 8.1, index 1): all critical points of index `1` are
traded for critical points of index `3`; the other critical points keep their indices. -/
theorem exists_no_index_one (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (h5 : 5 ≤ n)
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) (hsi : IsSelfIndexing I f a b)
    (hidx : ∀ x, f x ∈ Ioo a b → IsCriticalPt I f x → 0 < morseIndex I f x ∧ morseIndex I f x < n)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b)) (hV₀ : ConnectedSpace (f ⁻¹' {a})) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ IsSelfIndexing I g a b ∧
      (∀ x, g x ∈ Ioo a b → IsCriticalPt I g x →
        0 < morseIndex I g x ∧ morseIndex I g x < n ∧ morseIndex I g x ≠ 1) ∧
      ∀ x, g x ∈ Ioo a b → IsCriticalPt I g x → morseIndex I g x ≠ 3 →
        IsCriticalPt I f x ∧ morseIndex I g x = morseIndex I f x := by
  classical
  have key : ∀ N : ℕ, ∀ f : M → ℝ,
      {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x ∧ morseIndex I f x = 1}.ncard = N →
      MorseStrip I f a b → IsSelfIndexing I f a b →
      (∀ x, f x ∈ Ioo a b → IsCriticalPt I f x →
        0 < morseIndex I f x ∧ morseIndex I f x < n) →
      SimplyConnectedSpace (f ⁻¹' Icc a b) → ConnectedSpace (f ⁻¹' {a}) →
      ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ IsSelfIndexing I g a b ∧
        (∀ x, g x ∈ Ioo a b → IsCriticalPt I g x →
          0 < morseIndex I g x ∧ morseIndex I g x < n ∧ morseIndex I g x ≠ 1) ∧
        ∀ x, g x ∈ Ioo a b → IsCriticalPt I g x → morseIndex I g x ≠ 3 →
          IsCriticalPt I f x ∧ morseIndex I g x = morseIndex I f x := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro f hN hf hsi hidx hW hV₀
    have hfin : {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x ∧ morseIndex I f x = 1}.Finite :=
      hf.finite_critical.subset fun x hx => ⟨Ioo_subset_Icc_self hx.1, hx.2.1⟩
    by_cases hempty : {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x ∧ morseIndex I f x = 1} = ∅
    · refine ⟨f, ModifiedWithin.refl f a b, hf, hsi, fun x hx hc => ?_, fun x _ _ _ => ⟨‹_›, rfl⟩⟩
      refine ⟨(hidx x hx hc).1, (hidx x hx hc).2, fun h1 => ?_⟩
      have : x ∈ {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x ∧ morseIndex I f x = 1} := ⟨hx, hc, h1⟩
      rw [hempty] at this
      exact this
    · obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.2 hempty
      obtain ⟨g₁, hmod₁, hg₁, hsi₁, hcrit₁, hnot₁⟩ :=
        exists_trade_index_one_step I h5 hf hsi hidx hW hV₀ hp
      have hpre₁ : ∀ x, g₁ x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
        Set.ext_iff.1 hmod₁.preimage_Ioo x
      have hsub : {x | g₁ x ∈ Ioo a b ∧ IsCriticalPt I g₁ x ∧ morseIndex I g₁ x = 1} ⊂
          {x | f x ∈ Ioo a b ∧ IsCriticalPt I f x ∧ morseIndex I f x = 1} := by
        refine ⟨fun x hx => ?_, fun hle => hnot₁ (hle hp).2.1⟩
        rcases hcrit₁ x hx.1 hx.2.1 with h | h
        · exact ⟨(hpre₁ x).1 hx.1, h.1, h.2 ▸ hx.2.2⟩
        · exact absurd (hx.2.2.symm.trans h) (by norm_num)
      have hlt : {x | g₁ x ∈ Ioo a b ∧ IsCriticalPt I g₁ x ∧ morseIndex I g₁ x = 1}.ncard < N :=
        hN ▸ Set.ncard_lt_ncard hsub hfin
      have hidx₁ : ∀ x, g₁ x ∈ Ioo a b → IsCriticalPt I g₁ x →
          0 < morseIndex I g₁ x ∧ morseIndex I g₁ x < n := by
        intro x hx hc
        rcases hcrit₁ x hx hc with h | h
        · rw [h.2]
          exact hidx x ((hpre₁ x).1 hx) h.1
        · rw [h]
          exact ⟨by norm_num, by omega⟩
      have hW₁ : SimplyConnectedSpace (g₁ ⁻¹' Icc a b) := by
        rw [hmod₁.preimage_Icc]; exact hW
      have hV₁ : ConnectedSpace (g₁ ⁻¹' {a}) := by
        rw [hmod₁.preimage_singleton_left]; exact hV₀
      obtain ⟨g, hmod, hg, hsi', hidx', hcrit'⟩ :=
        ih _ hlt g₁ rfl hg₁ hsi₁ hidx₁ hW₁ hV₁
      have hpre : ∀ x, g x ∈ Ioo a b ↔ g₁ x ∈ Ioo a b := fun x =>
        Set.ext_iff.1 hmod.preimage_Ioo x
      refine ⟨g, hmod₁.trans hmod, hg, hsi', hidx', fun x hx hc h3 => ?_⟩
      obtain ⟨hc₁, heq₁⟩ := hcrit' x hx hc h3
      have hx₁ : g₁ x ∈ Ioo a b := (hpre x).1 hx
      rcases hcrit₁ x hx₁ hc₁ with h | h
      · exact ⟨h.1, heq₁.trans h.2⟩
      · exact absurd (heq₁.trans h) h3
  exact key _ f rfl hf hsi hidx hW hV₀

end PoincareHighDim
