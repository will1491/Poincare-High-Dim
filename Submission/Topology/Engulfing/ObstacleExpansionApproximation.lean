import Submission.Topology.Engulfing.ObstacleExpansionCompatibility
import Submission.Topology.Engulfing.ObstacleStellarApproximation

/-!
# A single obstacle model for expansions and general position

The model returned here carries the original source expansions, the embedded
fixed set, the obstacle faces, and the general-position map on one triangulation.
-/

namespace PoincareHighDim.Engulfing

open Set Geometry Topology

noncomputable section

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ} {K L : SimplicialComplex ℝ E}
  {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
  {f : C(K.space, EuclideanSpace ℝ (Fin n))}

theorem ObstacleAugmentationData.exists_compatible_generalPosition
    (a : ObstacleAugmentationData K L T f d p) (ha : a.PreservesSourceExpansions)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ObstacleAugmentationData K L T f d p, b.PreservesSourceExpansions ∧
      ∃ w : EuclideanSpace ℝ (Fin b.ambientDimension) → EuclideanSpace ℝ (Fin n),
      ∃ H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
      ∃ g : C(K.space, EuclideanSpace ℝ (Fin n)),
      (∀ s : Finset (EuclideanSpace ℝ (Fin b.ambientDimension)),
        (s : Set (EuclideanSpace ℝ (Fin b.ambientDimension))) ⊆ b.joint.vertices →
          s.card ≤ n + 1 → AffineIndependent ℝ (fun x : s => w x.val)) ∧
      (∀ x : b.joint.space, x.val ∈ b.fixedImage.space →
        correctedInterpolant b.joint b.joint_finite w H x = b.oldMap x) ∧
      (∀ x, g x = correctedInterpolant b.joint b.joint_finite w H (b.sourceMap x)) ∧
      (∀ x : K.space, x.val ∈ L.space → g x = f x) ∧
      (∀ x, ‖g x - f x‖ < ε) ∧
      (∀ y, ‖H y - y‖ < ε) ∧ (∀ y, ‖H.symm y - y‖ < ε) ∧
      (T.space = ⋃ s ∈ b.obstacleImage.faces,
        H '' convexHull ℝ (w '' (s : Set (EuclideanSpace ℝ (Fin b.ambientDimension))))) ∧
      (∀ s ∈ b.joint.faces, ∀ x y : b.joint.space,
        x.val ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin b.ambientDimension))) →
        y.val ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin b.ambientDimension))) →
        ‖interpolateVertices b.joint b.joint_finite w x -
          interpolateVertices b.joint b.joint_finite w y‖ < 5 * ε) := by
  obtain ⟨P, hP, hspace, w, H, g, href, hdim, hexp, hgp, hfixed, hg,
    hrel, hnear, hH, hHinv, hT, hPL, hosc⟩ := a.exists_stellar_approximation hε
  let b := a.refine P hP href hspace
  refine ⟨b, ha.refine P hP href hspace hexp, w, H, g,
    hgp, ?_, hg, hrel, hnear, hH, hHinv, hT, hosc⟩
  intro x hx
  apply hfixed x
  exact (a.refine_fixedImage_space P hP href hspace).subset hx

end

end PoincareHighDim.Engulfing
