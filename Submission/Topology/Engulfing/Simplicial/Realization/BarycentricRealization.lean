import Submission.Topology.Engulfing.Polyhedral.Quotient.PolyhedralQuotient
import Submission.Topology.Engulfing.Simplicial.Realization.GeometricRealization
import Submission.Topology.Engulfing.Simplicial.Barycentric.Subdivision.BarycentricCoverage

/-!
# Realizing abstract barycentric subdivision

The normalized indicator of a face is its standard centroid. Evaluation at these
centroids identifies the standard realization of the face-chain complex with the
original realization, preserving all subcomplexes.
-/

namespace PoincareHighDim.Engulfing

open Set Geometry Topology
open scoped BigOperators

noncomputable section

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The centroid coordinate vector, with value zero on the empty face. -/
def standardFaceCentroid (s : Finset ι) : ι → ℝ :=
  fun i => if i ∈ s then (s.card : ℝ)⁻¹ else 0

theorem standardFaceCentroid_eq_centroid {s : Finset ι} (hs : s.Nonempty) :
    standardFaceCentroid s = s.centroid ℝ (fun i => Pi.single i (1 : ℝ)) := by
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  ext i
  simp [standardFaceCentroid, Finset.centroidWeights_apply, Finset.sum_apply,
    Pi.smul_apply, Pi.single_apply]

theorem standardFaceCentroid_injective : Function.Injective (standardFaceCentroid : Finset ι → ι → ℝ) := by
  intro s t h
  apply Finset.Subset.antisymm
  · intro i hi
    by_contra hit
    have he := congrFun h i
    simp only [standardFaceCentroid, ite_eq_left hi, ite_eq_right hit] at he
    exact (inv_ne_zero (by exact_mod_cast (Finset.card_pos.mpr ⟨i, hi⟩).ne')) he
  · intro i hi
    by_contra his
    have he := congrFun h i
    simp only [standardFaceCentroid, ite_eq_left hi, ite_eq_right his] at he
    exact (inv_ne_zero (by exact_mod_cast (Finset.card_pos.mpr ⟨i, hi⟩).ne')) he.symm

theorem image_standardFaceCentroid_eq {C : Finset (Finset ι)} (hC : IsFaceChain C) :
    C.image standardFaceCentroid = chainCentroids (fun i => Pi.single i (1 : ℝ)) C := by
  classical
  unfold chainCentroids
  ext z
  simp only [Finset.mem_image]
  apply exists_congr
  intro s
  apply and_congr_right
  intro hs
  rw [standardFaceCentroid_eq_centroid (hC.1 s hs)]

private theorem affineIndependent_standardVertices :
    AffineIndependent ℝ (fun i : ι => Pi.single i (1 : ℝ)) := by
  convert (Pi.basisFun ℝ ι).linearIndependent.affineIndependent using 1
  funext i
  exact (Pi.basisFun_apply ℝ ι i).symm

/-- The actual geometric complex of face centroids. -/
def barycentricGeometricRealization (P : PreAbstractSimplicialComplex ι) :
    SimplicialComplex ℝ (ι → ℝ) where
  faces := ((abstractBarycentric P).map standardFaceCentroid).faces
  isRelLowerSet_faces := ((abstractBarycentric P).map standardFaceCentroid).isRelLowerSet_faces
  indep := by
    rintro s ⟨C, hC, rfl⟩
    change AffineIndependent ℝ (Subtype.val : C.image standardFaceCentroid → (ι → ℝ))
    rw [image_standardFaceCentroid_eq hC.2.1]
    exact hC.2.1.affineIndependent_chainCentroids affineIndependent_standardVertices
  inter_subset_convexHull := by
    rintro s t ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩
    dsimp only
    rw [image_standardFaceCentroid_eq hC.2.1, image_standardFaceCentroid_eq hD.2.1,
      hC.2.1.convexHull_chainCentroids_inter affineIndependent_standardVertices hD.2.1]
    apply convexHull_mono
    intro z hz
    obtain ⟨s, hs, rfl⟩ := mem_chainCentroids.mp hz
    exact ⟨mem_chainCentroids.mpr ⟨s, (Finset.mem_inter.mp hs).1, rfl⟩,
      mem_chainCentroids.mpr ⟨s, (Finset.mem_inter.mp hs).2, rfl⟩⟩

theorem barycentricGeometricRealization_space (P : PreAbstractSimplicialComplex ι) :
    (barycentricGeometricRealization P).space = (standardRealization P).space := by
  ext x
  constructor
  · intro hx
    obtain ⟨_, ⟨C, hC, rfl⟩, hxC⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨s, hs, hmax⟩ := hC.2.1.exists_largest hC.1
    refine (standardRealization_mem_space P x).mpr ⟨s, hC.2.2 s hs, ?_⟩
    apply convexHull_min (t := convexHull ℝ
      (s.image (fun i => Pi.single i (1 : ℝ)) : Set (ι → ℝ))) ?_
      (convex_convexHull ℝ _) hxC
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    rw [standardFaceCentroid_eq_centroid (hC.2.1.1 t ht),
      Finset.centroid_eq_centerMass _ (hC.2.1.1 t ht)]
    apply t.centerMass_mem_convexHull
    · intro i hi
      simp only [Finset.centroidWeights_apply, inv_nonneg, Nat.cast_nonneg]
    · rw [t.sum_centroidWeights_eq_one_of_nonempty ℝ (hC.2.1.1 t ht)]
      norm_num
    · intro i hi
      exact Finset.mem_image.mpr ⟨i, hmax t ht hi, rfl⟩
  · intro hx
    obtain ⟨s, hs, hxs⟩ := (standardRealization_mem_space P x).mp hx
    have hcoords := (mem_standardFace_iff s x).mp hxs
    have hsum : ∑ i ∈ s, x i = 1 := by
      rw [← hcoords.1.2]
      exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hcoords.2 i hi)
    obtain ⟨C, hCne, hC, hCs, hCx⟩ := exists_faceChain_of_weights
      (fun i => Pi.single i (1 : ℝ)) s x (fun i _ => hcoords.1.1 i) hsum
    have he : (∑ i ∈ s, x i • Pi.single i (1 : ℝ)) = x := by
      rw [Finset.sum_subset (Finset.subset_univ s)
        (fun i _ hi => by rw [hcoords.2 i hi, zero_smul])]
      ext i
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    rw [he] at hCx
    apply SimplicialComplex.mem_space_iff.mpr
    refine ⟨C.image standardFaceCentroid,
      ⟨C, ⟨hCne, hC, fun t ht => (P.isRelLowerSet_faces hs).2 (hCs t ht) (hC.1 t ht)⟩, rfl⟩, ?_⟩
    rwa [image_standardFaceCentroid_eq hC]

/-- Subdivision is a homeomorphism in standard coordinates. -/
def barycentricRealizationHomeomorph (P : PreAbstractSimplicialComplex ι) :
    (standardRealization (abstractBarycentric P)).space ≃ₜ (standardRealization P).space :=
  (geometricRealizationHomeomorph (abstractBarycentric P) standardFaceCentroid
    standardFaceCentroid_injective (barycentricGeometricRealization P) rfl).trans
      (Homeomorph.setCongr (barycentricGeometricRealization_space P))

@[simp] theorem barycentricRealizationHomeomorph_apply
    (P : PreAbstractSimplicialComplex ι)
    (x : (standardRealization (abstractBarycentric P)).space) :
    (barycentricRealizationHomeomorph P x).val = vertexEvaluation standardFaceCentroid x.val := rfl

theorem barycentricEvaluation_image_space (P : PreAbstractSimplicialComplex ι) :
    vertexEvaluation standardFaceCentroid '' (standardRealization (abstractBarycentric P)).space =
      (standardRealization P).space :=
  (vertexEvaluation_image_space (abstractBarycentric P) standardFaceCentroid
    (barycentricGeometricRealization P) rfl).trans (barycentricGeometricRealization_space P)

/-- The centroid homeomorphism identifies the realization of every subcomplex. -/
theorem barycentricRealizationHomeomorph_mem_subcomplex_iff
    (P D : PreAbstractSimplicialComplex ι) (hDP : D ≤ P)
    (x : (standardRealization (abstractBarycentric P)).space) :
    (barycentricRealizationHomeomorph P x).val ∈ (standardRealization D).space ↔
      x.val ∈ (standardRealization (abstractBarycentric D)).space := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (barycentricEvaluation_image_space D).symm.subset hx
    have hyP := standardRealization_mono (abstractBarycentric_mono hDP) hy
    have he : y = x.val := vertexEvaluation_injOn_space (abstractBarycentric P)
      standardFaceCentroid standardFaceCentroid_injective (barycentricGeometricRealization P)
        rfl hyP x.property hyx
    exact he ▸ hy
  · intro hx
    exact (barycentricEvaluation_image_space D).subset (mem_image_of_mem _ hx)

theorem standardFaceCentroid_eq_smul_sum (s : Finset ι) :
    standardFaceCentroid s = (s.card : ℝ)⁻¹ • ∑ i ∈ s, Pi.single i (1 : ℝ) := by
  ext i
  simp [standardFaceCentroid, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]

theorem vertexPushforward_standardFaceCentroid (q : ι → κ) (s : Finset ι)
    (hq : (s : Set ι).InjOn q) :
    vertexPushforward q (standardFaceCentroid s) = standardFaceCentroid (s.image q) := by
  rw [standardFaceCentroid_eq_smul_sum, map_smul, map_sum]
  simp_rw [vertexPushforward_single]
  rw [standardFaceCentroid_eq_smul_sum, Finset.card_image_of_injOn hq, Finset.sum_image hq]

theorem vertexEvaluation_vertexPushforward {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : κ → E) (q : ι → κ) (x : ι → ℝ) :
    vertexEvaluation v (vertexPushforward q x) = vertexEvaluation (v ∘ q) x := by
  have he : (vertexEvaluation v).comp (vertexPushforward q) = vertexEvaluation (v ∘ q) := by
    apply (Pi.basisFun ℝ ι).ext
    intro i
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, vertexPushforward_single]
    simp [vertexEvaluation, Fintype.linearCombination_apply]
  exact LinearMap.congr_fun he x

/-- Centroid evaluation commutes with a simplicial map that is nondegenerate on each face. -/
theorem barycentricEvaluation_natural (P : PreAbstractSimplicialComplex ι) (q : ι → κ)
    (hq : ∀ s ∈ P.faces, (s : Set ι).InjOn q)
    {x : Finset ι → ℝ} (hx : x ∈ (standardRealization (abstractBarycentric P)).space) :
    vertexPushforward q (vertexEvaluation standardFaceCentroid x) =
      vertexEvaluation standardFaceCentroid (vertexPushforward (fun s : Finset ι => s.image q) x) := by
  rw [vertexEvaluation_vertexPushforward]
  obtain ⟨C, hC, hxC⟩ := (standardRealization_mem_space _ _).mp hx
  have hxzero := (mem_standardFace_iff C x).mp hxC |>.2
  change vertexPushforward q (∑ s, x s • standardFaceCentroid s) =
    ∑ s, x s • standardFaceCentroid (s.image q)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul]
  by_cases hs : s ∈ C
  · rw [vertexPushforward_standardFaceCentroid q s (hq s (hC.2.2 s hs))]
  · rw [hxzero s hs]
    simp

def doubleBarycentricEvaluation : (Finset (Finset ι) → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  (vertexEvaluation (standardFaceCentroid : Finset ι → ι → ℝ)).comp
    (vertexEvaluation standardFaceCentroid)

def doubleBarycentricRealizationHomeomorph (P : PreAbstractSimplicialComplex ι) :
    (standardRealization (abstractBarycentric (abstractBarycentric P))).space ≃ₜ
      (standardRealization P).space :=
  (barycentricRealizationHomeomorph (abstractBarycentric P)).trans
    (barycentricRealizationHomeomorph P)

@[simp] theorem doubleBarycentricRealizationHomeomorph_apply
    (P : PreAbstractSimplicialComplex ι)
    (x : (standardRealization (abstractBarycentric (abstractBarycentric P))).space) :
    (doubleBarycentricRealizationHomeomorph P x).val = doubleBarycentricEvaluation x.val := rfl

theorem doubleBarycentricRealizationHomeomorph_mem_subcomplex_iff
    (P D : PreAbstractSimplicialComplex ι) (hDP : D ≤ P)
    (x : (standardRealization (abstractBarycentric (abstractBarycentric P))).space) :
    (doubleBarycentricRealizationHomeomorph P x).val ∈ (standardRealization D).space ↔
      x.val ∈ (standardRealization (abstractBarycentric (abstractBarycentric D))).space := by
  change (barycentricRealizationHomeomorph P
    (barycentricRealizationHomeomorph (abstractBarycentric P) x)).val ∈ _ ↔ _
  rw [barycentricRealizationHomeomorph_mem_subcomplex_iff P D hDP,
    barycentricRealizationHomeomorph_mem_subcomplex_iff _ _ (abstractBarycentric_mono hDP)]

theorem faceImage_injOn_barycentric (P : PreAbstractSimplicialComplex ι) (q : ι → κ)
    (hq : ∀ s ∈ P.faces, (s : Set ι).InjOn q) :
    ∀ C ∈ (abstractBarycentric P).faces,
      (C : Set (Finset ι)).InjOn (fun s : Finset ι => s.image q) := by
  intro C hC s hs t ht heq
  exact faceImage_injOn_barycentric_subcomplex P P q hq C hC
    ⟨hs, hC.2.2 s hs⟩ ⟨ht, hC.2.2 t ht⟩ heq

theorem doubleBarycentricEvaluation_natural (P : PreAbstractSimplicialComplex ι) (q : ι → κ)
    (hq : ∀ s ∈ P.faces, (s : Set ι).InjOn q)
    {x : Finset (Finset ι) → ℝ}
    (hx : x ∈ (standardRealization (abstractBarycentric (abstractBarycentric P))).space) :
    vertexPushforward q (doubleBarycentricEvaluation x) =
      doubleBarycentricEvaluation
        (vertexPushforward (fun C : Finset (Finset ι) => C.image (fun s => s.image q)) x) := by
  have hx' := (barycentricEvaluation_image_space (abstractBarycentric P)).subset
    (mem_image_of_mem (vertexEvaluation standardFaceCentroid) hx)
  change vertexPushforward q (vertexEvaluation standardFaceCentroid
    (vertexEvaluation standardFaceCentroid x)) =
    vertexEvaluation standardFaceCentroid (vertexEvaluation standardFaceCentroid
      (vertexPushforward (fun C : Finset (Finset ι) => C.image (fun s => s.image q)) x))
  rw [barycentricEvaluation_natural P q hq hx',
    barycentricEvaluation_natural (abstractBarycentric P) _ (faceImage_injOn_barycentric P q hq) hx]

theorem doubleFaceImage_mem_space (P : PreAbstractSimplicialComplex ι) (q : ι → κ)
    {x : Finset (Finset ι) → ℝ}
    (hx : x ∈ (standardRealization (abstractBarycentric (abstractBarycentric P))).space) :
    vertexPushforward (fun C : Finset (Finset ι) => C.image (fun s => s.image q)) x ∈
      (standardRealization (abstractBarycentric (abstractBarycentric (P.map q)))).space := by
  rw [abstractBarycentric_map, abstractBarycentric_map]
  exact (vertexPushforward_image_space _ _).subset (mem_image_of_mem _ hx)

/-- Equality of the double-subdivision images is exactly equality of the original images. -/
theorem doubleFaceImage_eq_iff (P : PreAbstractSimplicialComplex ι) (q : ι → κ)
    (hq : ∀ s ∈ P.faces, (s : Set ι).InjOn q)
    {x y : Finset (Finset ι) → ℝ}
    (hx : x ∈ (standardRealization (abstractBarycentric (abstractBarycentric P))).space)
    (hy : y ∈ (standardRealization (abstractBarycentric (abstractBarycentric P))).space) :
    vertexPushforward (fun C : Finset (Finset ι) => C.image (fun s => s.image q)) x =
        vertexPushforward (fun C : Finset (Finset ι) => C.image (fun s => s.image q)) y ↔
      vertexPushforward q (doubleBarycentricEvaluation x) =
        vertexPushforward q (doubleBarycentricEvaluation y) := by
  rw [doubleBarycentricEvaluation_natural P q hq hx,
    doubleBarycentricEvaluation_natural P q hq hy]
  constructor
  · exact congrArg doubleBarycentricEvaluation
  · intro h
    exact congrArg Subtype.val ((doubleBarycentricRealizationHomeomorph (P.map q)).injective
      (show doubleBarycentricRealizationHomeomorph (P.map q)
          ⟨_, doubleFaceImage_mem_space P q hx⟩ =
        doubleBarycentricRealizationHomeomorph (P.map q)
          ⟨_, doubleFaceImage_mem_space P q hy⟩ from Subtype.ext h))

end

end PoincareHighDim.Engulfing
