import Submission.Topology.Engulfing.ObstacleSourceSubdivision
import Submission.Topology.Engulfing.ObstacleRefinement
import Submission.Topology.Engulfing.ExpansionImageRefinement
import Submission.Topology.Engulfing.RelativeTriangulationExtension

/-!
# Expansion compatibility of the joint obstacle model

Refine the embedded source before extending that triangulation to the joint
source. The resulting model retains every finite expansion of the original
source, so subsequent stellar general-position approximation can preserve it.
-/

namespace PoincareHighDim.Engulfing

open Set Geometry Topology

noncomputable section

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ} {K L : SimplicialComplex ℝ E}
  {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
  {f : C(K.space, EuclideanSpace ℝ (Fin n))}

def ObstacleAugmentationData.PreservesSourceExpansions
    (a : ObstacleAugmentationData K L T f d p) : Prop :=
  ∀ A C, C ⊆ K.space → FiniteSimplexExpansionIn K A C →
    FiniteSimplexExpansionIn a.joint
      ((fun x : K.space => (a.sourceMap x).val) '' (Subtype.val ⁻¹' A))
      ((fun x : K.space => (a.sourceMap x).val) '' (Subtype.val ⁻¹' C))

omit [FiniteDimensional ℝ E] in
theorem ObstacleAugmentationData.PreservesSourceExpansions.refine
    {a : ObstacleAugmentationData K L T f d p} (h : a.PreservesSourceExpansions)
    (P : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)))
    (hP : P.faces.Finite) (href : SimplicialRefines P a.joint)
    (hspace : P.space = a.joint.space)
    (hexp : ∀ A C, FiniteSimplexExpansionIn a.joint A C → FiniteSimplexExpansionIn P A C) :
    (a.refine P hP href hspace).PreservesSourceExpansions := by
  intro A C hC he
  exact hexp _ _ (h A C hC he)

theorem ObstacleAugmentationData.exists_preserving_source_expansions_of_relative_extension
    (a : ObstacleAugmentationData K L T f d p) (hK : K.faces.Finite)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (hextend : ∀ J : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)),
      J.faces.Finite → J.space = a.sourceImage.space → SimplicialRefines J a.sourceImage →
      ∃ P : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)),
        P.faces.Finite ∧ P.space = a.joint.space ∧ SimplicialRefines P a.joint ∧
        J.faces ⊆ P.faces) :
    ∃ b : ObstacleAugmentationData K L T f d p, b.PreservesSourceExpansions := by
  obtain ⟨j, J, hj, hJ, hJs, hJref, hJdim, hJexp⟩ :=
    exists_image_refinement_preserving_expansions K a.sourceImage hK
      (a.joint_finite.subset a.sourceImage_faces) a.sourceHomeomorph
      a.sourceHomeomorph_affine_inverse hd
  obtain ⟨P, hP, hPs, href, hJP⟩ := hextend J hJ hJs hJref
  let b := a.refine P hP href hPs
  have himage (A : Set E) (hA : A ⊆ K.space) :
      j '' A = (fun x : K.space => (a.sourceMap x).val) '' (Subtype.val ⁻¹' A) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hA hx⟩, hx, (hj ⟨x, hA hx⟩).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, hj x⟩
  refine ⟨b, ?_⟩
  intro A C hC he
  have h := (hJexp A C hC he).mono hJP
  rw [himage A (he.subset.trans hC), himage C hC] at h
  exact h

theorem ObstacleAugmentationData.exists_preserving_source_expansions
    (a : ObstacleAugmentationData K L T f d p) (hK : K.faces.Finite)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ b : ObstacleAugmentationData K L T f d p, b.PreservesSourceExpansions := by
  apply a.exists_preserving_source_expansions_of_relative_extension hK hd
  intro J hJ hJs hJD
  obtain ⟨P, hP, hPs, href, hJP, hdim⟩ := exists_relative_triangulation
    a.joint a.sourceImage J a.joint_finite a.sourceImage_faces hJ hJD hJs a.joint_dimension
  exact ⟨P, hP, hPs, href, hJP⟩

end

end PoincareHighDim.Engulfing
