import Submission.Topology.Engulfing.NewmanGlobalData
import Submission.Topology.Engulfing.NewmanInduction
import Submission.Topology.SphereHigherConnectivity
import Mathlib.Topology.Homotopy.Path

/-!
# The relative engulfing induction problem

The inert source may have one more dimension than the target. This is needed
when a membrane has been attached before invoking the lower-dimensional case.
Only the target and obstacle have the codimension-three bound.
-/

namespace PoincareHighDim.Engulfing

open Set Metric Geometry Topology
open scoped ContinuousMap

variable {M : Type*} [TopologicalSpace M]

/-- The two sphere-extension ranges used to attach membranes. Nonemptiness of
the open set is explicit, including when the target consists only of points. -/
structure NewmanConnectivity (M : Type*) [TopologicalSpace M] (U : Set M) (p : ℕ) : Prop where
  nonempty : U.Nonempty
  ambient : ∀ k : ℕ, k ≤ p →
    ∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, M), f.Nullhomotopic
  inside : ∀ k : ℕ, k + 1 ≤ p →
    ∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, U), f.Nullhomotopic

/-- Engulfing changes the open set by a homeomorphism, which preserves both
connectivity hypotheses. -/
theorem NewmanConnectivity.image {U : Set M} {p : ℕ}
    (h : NewmanConnectivity M U p) (e : M ≃ₜ M) : NewmanConnectivity M (e '' U) p := by
  refine ⟨h.nonempty.image e, h.ambient, ?_⟩
  intro k hk f
  let q := e.image U
  let qf : C(U, e '' U) := ⟨q, q.continuous⟩
  let qi : C(e '' U, U) := ⟨q.symm, q.symm.continuous⟩
  have hnull := (h.inside k hk (qi.comp f)).comp_right qf
  have heq : qf.comp (qi.comp f) = f := by
    ext x
    exact congrArg Subtype.val (q.apply_symm_apply (f x))
  rwa [heq] at hnull

theorem NewmanConnectivity.mono {U : Set M} {p r : ℕ}
    (h : NewmanConnectivity M U p) (hrp : r ≤ p) : NewmanConnectivity M U r :=
  ⟨h.nonempty, fun k hk => h.ambient k (hk.trans hrp),
    fun k hk => h.inside k (hk.trans hrp)⟩

/-- The zeroth ambient sphere condition supplies paths for the one-vertex
membrane case. -/
theorem NewmanConnectivity.pathConnectedSpace {U : Set M} {p : ℕ}
    (h : NewmanConnectivity M U p) : PathConnectedSpace M := by
  classical
  refine ⟨h.nonempty.to_subtype.map Subtype.val, fun x y => ?_⟩
  let S := sphere (0 : EuclideanSpace ℝ (Fin 1)) 1
  have hnonzero (z : S) : z.1 0 ≠ 0 := by
    intro hz
    have hzero : z.1 = 0 := by
      ext i
      fin_cases i
      exact hz
    have hnorm := mem_sphere_zero_iff_norm.mp z.2
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  let A : Set S := {z | 0 < z.1 0}
  have hAopen : IsOpen A := isOpen_lt continuous_const (by fun_prop)
  have hAclosed : IsClosed A := by
    rw [← isOpen_compl_iff]
    have heq : Aᶜ = {z : S | z.1 0 < 0} := by
      ext z
      change (¬ 0 < z.1 0) ↔ z.1 0 < 0
      exact ⟨fun hz => lt_of_le_of_ne (le_of_not_gt hz) (hnonzero z),
        fun hz => not_lt_of_ge hz.le⟩
    rw [heq]
    exact isOpen_lt (by fun_prop) continuous_const
  have hA : IsClopen A := ⟨hAclosed, hAopen⟩
  let f : C(S, M) := ⟨fun z => if z ∈ A then x else y,
    continuous_const.if (fun z hz => by
      change z ∈ frontier A at hz
      rw [hA.frontier_eq] at hz
      exact hz.elim) continuous_const⟩
  let a : S := ⟨EuclideanSpace.single 0 (1 : ℝ), by simp [S]⟩
  let b : S := ⟨-EuclideanSpace.single 0 (1 : ℝ), by simp [S]⟩
  have ha : f a = x := by simp [f, A, a]
  have hb : f b = y := by simp [f, A, b]
  obtain ⟨c, ⟨H⟩⟩ := h.ambient 0 (Nat.zero_le p) f
  have hxa : Joined (f a) c := ⟨H.evalAt a⟩
  have hyb : Joined (f b) c := ⟨H.evalAt b⟩
  simpa only [ha, hb] using hxa.trans hyb.symm

section Problem

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace M]

/-- The full data for one relative engulfing problem, with remaining face-card
complexity `q`. The source is allowed the extra membrane dimension. -/
structure NewmanProblem (n p q : ℕ) where
  source : SimplicialComplex ℝ E
  fixed : SimplicialComplex ℝ E
  target : SimplicialComplex ℝ E
  source_finite : source.faces.Finite
  fixed_subcomplex : fixed.faces ⊆ source.faces
  target_subcomplex : target.faces ⊆ source.faces
  source_dimension : ∀ s ∈ source.faces, s.card ≤ p + 2
  target_dimension : ∀ s ∈ target.faces, s.card ≤ p + 1
  map : C(source.space, M)
  fixed_injective : InjOn map (Subtype.val ⁻¹' fixed.space)
  obstacle : Set M
  openSet : Set M
  obstacle_closed : IsClosed obstacle
  open_openSet : IsOpen openSet
  obstacle_subset : obstacle ⊆ openSet
  localData : HasLocalPLData source fixed map obstacle n p
  codimension : p + 3 ≤ n
  connectivity : NewmanConnectivity M openSet p
  decomposition : EngulfingDecomposition source target map openSet q

variable {E M}

def NewmanProblem.Conclusion {n p q : ℕ} (P : NewmanProblem E M n p q) (ε : ℝ) : Prop :=
  NewmanConclusion P.source P.fixed P.target P.map P.obstacle P.openSet ε

end Problem

variable (M : Type*) [MetricSpace M]

/-- The dimension-induction assertion is uniform in the finite-dimensional
Euclidean source, since attaching a cone and taking a quotient change it. -/
def RelativeNewmanAt (n p q : ℕ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    ∀ P : NewmanProblem E M n p q, ∀ ε : ℝ, 0 < ε → P.Conclusion ε

/-- The zero-complexity case has no motion and no map perturbation. -/
theorem relativeNewmanAt_zero (n p : ℕ) : RelativeNewmanAt M n p 0 := by
  intro E _ _ _ P ε hε
  exact newmanConclusion_of_zero_complexity P.source P.fixed P.target P.map
    P.obstacle_subset P.decomposition.to_outsideDimension hε

/-- The isolated top-face case. All other target faces have already been
covered, and the face to move is disjoint from the obstacle. -/
def SingleSimplexNewmanAt (n p q : ℕ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    ∀ P : NewmanProblem E M n p (q + 1), ∀ s : Finset E,
      s ∈ P.target.faces → s.card = q + 1 →
      (∀ t ∈ P.target.faces, t ≠ s →
        ∀ x : P.source.space, x.1 ∈ convexHull ℝ (t : Set E) → P.map x ∈ P.openSet) →
      Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.obstacle →
      ∀ ε : ℝ, 0 < ε → P.Conclusion ε

/-- Above the target dimension there is no simplex to which the isolated-face
step could apply. -/
theorem singleSimplexNewmanAt_of_lt {n p q : ℕ} (hpq : p < q) :
    SingleSimplexNewmanAt M n p q := by
  intro E _ _ _ P s hs hcard
  have hdim := P.target_dimension s hs
  omega

end PoincareHighDim.Engulfing
