/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Finite configurations in general position

Finite configurations in Euclidean space may be perturbed arbitrarily little so that every
subfamily of at most one more than the ambient dimension is affinely independent.
-/

namespace PoincareHighDim.Engulfing

open Set Metric Topology

variable {n : ℕ} {ι : Type*}

/-- The complement of a proper affine subspace of Euclidean space is dense. -/
theorem dense_compl_affineSubspace (s : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
    (hs : s ≠ ⊤) : Dense (s : Set (EuclideanSpace ℝ (Fin n)))ᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  apply hs
  apply top_unique
  rw [← isOpen_interior.affineSpan_eq_top ⟨x, hx⟩]
  exact affineSpan_le.mpr interior_subset

/-- Avoid simultaneously the affine spans of all subfamilies of size at most `n` among a
fixed finite collection, while remaining in any prescribed ball. -/
theorem exists_near_avoiding_affineSpans [DecidableEq ι] (s : Finset ι)
    (v : ι → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y, ‖y - x‖ < ε ∧ ∀ t : Finset ι, t ⊆ s → t.card ≤ n →
      y ∉ affineSpan ℝ (v '' (t : Set ι)) := by
  let T := s.powerset.filter (fun t => t.card ≤ n)
  let F (t : T) : Set (EuclideanSpace ℝ (Fin n)) :=
    (affineSpan ℝ (v '' (t.1 : Set ι)) : Set (EuclideanSpace ℝ (Fin n)))ᶜ
  have hopen (t : T) : IsOpen (F t) :=
    (AffineSubspace.closed_of_finiteDimensional _).isOpen_compl
  have hdense (t : T) : Dense (F t) := by
    apply dense_compl_affineSubspace
    apply affineSpan_image_ne_top_of_encard_le_finrank ℝ t.1.finite_toSet
    have ht : t.1.card ≤ n := (Finset.mem_filter.mp t.2).2
    simpa using (show (t.1.card : ℕ∞) ≤ n by exact_mod_cast ht)
  obtain ⟨y, hball, hy⟩ := (dense_iInter_of_isOpen hopen hdense).inter_open_nonempty
    (ball x ε) isOpen_ball ⟨x, mem_ball_self hε⟩
  refine ⟨y, (mem_ball_iff_norm.mp hball), ?_⟩
  intro t hts htn
  exact mem_iInter.mp hy ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hts, htn⟩⟩

set_option maxHeartbeats 800000 in
/-- Add a point outside the affine span of an independent finite family. -/
theorem affineIndependent_finset_insert [DecidableEq ι] {s : Finset ι} {a : ι}
    (_ha : a ∉ s) {v : ι → EuclideanSpace ℝ (Fin n)}
    (hv : AffineIndependent ℝ (fun i : s => v i)) {p : EuclideanSpace ℝ (Fin n)}
    (hp : p ∉ affineSpan ℝ (v '' (s : Set ι))) :
    AffineIndependent ℝ (fun i : (insert a s : Finset ι) => Function.update v a p i) := by
  let j : (insert a s : Finset ι) := ⟨a, Finset.mem_insert_self a s⟩
  let E : {z : (insert a s : Finset ι) // z ≠ j} ↪ s := {
    toFun := fun z => ⟨z.1.1, (Finset.mem_insert.mp z.1.2).resolve_left
      (fun h => z.2 (Subtype.ext h))⟩
    inj' := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : s => (z : ι)) h)) }
  have hsub : AffineIndependent ℝ
      (fun z : {z : (insert a s : Finset ι) // z ≠ j} => Function.update v a p z.1) := by
    convert hv.comp_embedding E using 1
    funext z
    have hza : (z.1 : ι) ≠ a := fun h => z.2 (Subtype.ext h)
    exact Function.update_of_ne hza _ _
  apply hsub.affineIndependent_of_notMem_span
  change Function.update v a p a ∉ _
  simp only [Function.update_self]
  intro hh
  apply hp
  apply affineSpan_mono ℝ ?_ hh
  rintro _ ⟨z, hz, rfl⟩
  have hza : (z : ι) ≠ a := fun h => hz (Subtype.ext h)
  refine ⟨z, (Finset.mem_insert.mp z.2).resolve_left hza, ?_⟩
  exact (Function.update_of_ne hza _ _).symm

/-- General position on a finite set of indices. -/
def InGeneralPositionOn (s : Finset ι) (v : ι → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ t : Finset ι, t ⊆ s → t.card ≤ n + 1 → AffineIndependent ℝ (fun i : t => v i)

/-- Perturb the vertices in a finite set into general position, leaving all other vertices
fixed. Each prescribed positive error bound is respected separately. -/
theorem exists_generalPositionOn [DecidableEq ι] (s : Finset ι)
    (v : ι → EuclideanSpace ℝ (Fin n)) (ε : ι → ℝ) (hε : ∀ i ∈ s, 0 < ε i) :
    ∃ w : ι → EuclideanSpace ℝ (Fin n),
      (∀ i ∈ s, ‖w i - v i‖ < ε i) ∧ (∀ i ∉ s, w i = v i) ∧
      InGeneralPositionOn s w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨v, by simp, by simp, ?_⟩
      intro t ht _
      have : t = ∅ := Finset.subset_empty.mp ht
      subst t
      exact affineIndependent_of_subsingleton ℝ _
  | @insert a s ha ih =>
      obtain ⟨w, hw, hfix, hgp⟩ := ih (fun i hi => hε i (Finset.mem_insert_of_mem hi))
      obtain ⟨p, hpnear, hpavoid⟩ := exists_near_avoiding_affineSpans s w (v a)
        (hε a (Finset.mem_insert_self a s))
      refine ⟨Function.update w a p, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simpa using hpnear
        · rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
          exact hw i hi
      · intro i hi
        have hia : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self a s)
        rw [Function.update_of_ne hia]
        exact hfix i (fun his => hi (Finset.mem_insert_of_mem his))
      · intro t ht hcard
        by_cases hat : a ∈ t
        · have hts : t.erase a ⊆ s := by
            intro i hi
            have hi' := Finset.mem_erase.mp hi
            exact (Finset.mem_insert.mp (ht hi'.2)).resolve_left hi'.1
          have htcard : (t.erase a).card ≤ n := by
            rw [Finset.card_erase_of_mem hat]
            have := Finset.card_pos.mpr ⟨a, hat⟩
            omega
          have hgp' := affineIndependent_finset_insert (Finset.notMem_erase a t)
            (hgp (t.erase a) hts (by omega)) (hpavoid (t.erase a) hts htcard)
          exact (congrArg (fun S : Finset ι => AffineIndependent ℝ
            (fun i : S => Function.update w a p i)) (Finset.insert_erase hat)).mp hgp'
        · have hts : t ⊆ s := by
            intro i hi
            exact (Finset.mem_insert.mp (ht hi)).resolve_left (fun h => hat (h ▸ hi))
          have heq : (fun i : t => Function.update w a p i) = (fun i : t => w i) := by
            funext i
            have hia : (i : ι) ≠ a := fun h => hat (h ▸ i.2)
            exact Function.update_of_ne hia _ _
          rw [heq]
          exact hgp t hts hcard

/-- Every finite Euclidean configuration can be perturbed arbitrarily little into general
position: every subfamily of at most `n + 1` vertices is affinely independent. -/
theorem exists_generalPosition {N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin n))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : Fin N → EuclideanSpace ℝ (Fin n), (∀ i, ‖w i - v i‖ < ε) ∧
      ∀ s : Finset (Fin N), s.card ≤ n + 1 → AffineIndependent ℝ (fun i : s => w i) := by
  obtain ⟨w, hw, -, hgp⟩ := exists_generalPositionOn Finset.univ v (fun _ => ε)
    (fun _ _ => hε)
  exact ⟨w, fun i => hw i (Finset.mem_univ i), fun s hs => hgp s (Finset.subset_univ s) hs⟩

end PoincareHighDim.Engulfing
