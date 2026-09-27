import Submission.Topology.Engulfing.Simplicial.Barycentric.Subdivision.BarycentricComplexSubdivision
import Submission.Topology.Engulfing.Simplicial.Barycentric.Coordinates.BarycentricMesh
import Mathlib.Order.Interval.Finset.Nat

/-!
# Arbitrarily fine finite subdivisions

Iterating geometric barycentric subdivision preserves the realization and gives uniformly
small faces, each lying in an original face.
-/

namespace PoincareHighDim.Engulfing

set_option linter.unusedSectionVars false

open Set Metric Topology

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A chain of nonempty subfaces has at most as many members as its parent has vertices. -/
theorem IsFaceChain.card_le_parent {ι : Type*} [DecidableEq ι]
    {C : Finset (Finset ι)} (hC : IsFaceChain C) {T : Finset ι}
    (hT : ∀ s ∈ C, s ⊆ T) : C.card ≤ T.card := by
  have hmap : Set.MapsTo Finset.card (C : Set (Finset ι))
      (Finset.Icc 1 T.card : Finset ℕ) := by
    intro s hs
    exact Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr (hC.1 s hs),
      Finset.card_le_card (hT s hs)⟩
  have hinj : (C : Set (Finset ι)).InjOn Finset.card := by
    intro s hs t ht heq
    rcases hC.2 s hs t ht with hst | hts
    · exact Finset.eq_of_subset_of_card_le hst heq.ge
    · exact (Finset.eq_of_subset_of_card_le hts heq.le).symm
  simpa using Finset.card_le_card_of_injOn Finset.card hmap hinj

/-- Subdivision preserves any given face dimension bound, independently of the ambient space. -/
theorem barycentricSubdivision_face_card_le (K : Geometry.SimplicialComplex ℝ E)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∀ s ∈ (barycentricSubdivision K).faces, s.card ≤ d + 1 := by
  classical
  rintro s ⟨C, hCne, hC, hCK, rfl⟩
  obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
  have himage : (chainCentroids (id : E → E) C).card ≤ C.card := by
    unfold chainCentroids
    exact @Finset.card_image_le (Finset E) E C (fun s => s.centroid ℝ id)
      (Classical.decEq E)
  exact himage.trans ((hC.card_le_parent hCV).trans (hd V (hCK V hVC)))

/-- Each face of a refinement lies geometrically in some face of the original complex. -/
def SimplicialRefines (L K : Geometry.SimplicialComplex ℝ E) : Prop :=
  ∀ s ∈ L.faces, ∃ t ∈ K.faces,
    convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)

theorem SimplicialRefines.refl (K : Geometry.SimplicialComplex ℝ E) : SimplicialRefines K K :=
  fun s hs => ⟨s, hs, subset_rfl⟩

theorem SimplicialRefines.trans {L K J : Geometry.SimplicialComplex ℝ E}
    (hLK : SimplicialRefines L K) (hKJ : SimplicialRefines K J) : SimplicialRefines L J := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hLK s hs
  obtain ⟨u, hu, htu⟩ := hKJ t ht
  exact ⟨u, hu, hst.trans htu⟩

theorem barycentricSubdivision_refines (K : Geometry.SimplicialComplex ℝ E) :
    SimplicialRefines (barycentricSubdivision K) K := by
  rintro s ⟨C, hCne, hC, hCK, rfl⟩
  obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
  exact ⟨V, hCK V hVC, hC.convexHull_chainCentroids_subset V hCV⟩

/-- A uniform upper bound on the diameters of the geometric faces. -/
def HasMeshLE (K : Geometry.SimplicialComplex ℝ E) (D : ℝ) : Prop :=
  ∀ s ∈ K.faces, diam (convexHull ℝ (s : Set E)) ≤ D

theorem exists_mesh_bound (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    ∃ D : ℝ, 0 ≤ D ∧ HasMeshLE K D := by
  obtain ⟨D, hD⟩ := (hK.image (fun s : Finset E => diam (convexHull ℝ (s : Set E)))).bddAbove
  exact ⟨max D 0, le_max_right _ _, fun s hs =>
    (hD (mem_image_of_mem _ hs)).trans (le_max_left _ _)⟩

/-- The intrinsic face dimension determines the mesh contraction factor. -/
theorem HasMeshLE.barycentricSubdivision_of_face_card_le
    {K : Geometry.SimplicialComplex ℝ E} {D : ℝ} (hK : HasMeshLE K D) (hD : 0 ≤ D)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    HasMeshLE (barycentricSubdivision K) ((d : ℝ) / (d + 1) * D) := by
  classical
  rintro s ⟨C, hCne, hC, hCK, rfl⟩
  obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
  have hV : V ∈ K.faces := hCK V hVC
  have hdist : ∀ i ∈ V, ∀ j ∈ V, dist (id i) (id j) ≤ D := by
    intro i hi j hj
    exact (dist_le_diam_of_mem (isBounded_convexHull.mpr V.finite_toSet.isBounded)
      (subset_convexHull ℝ _ hi) (subset_convexHull ℝ _ hj)).trans (hK V hV)
  have h := hC.diam_convexHull_centroids_le id (hd V hV) hCV hD hdist
  simpa only [chainCentroids, Finset.coe_image] using h

/-- One subdivision contracts the mesh by the ambient-dimension factor. -/
theorem HasMeshLE.barycentricSubdivision [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {D : ℝ} (hK : HasMeshLE K D) (hD : 0 ≤ D) :
    HasMeshLE (barycentricSubdivision K)
      ((Module.finrank ℝ E : ℝ) / (Module.finrank ℝ E + 1) * D) := by
  classical
  rintro s ⟨C, hCne, hC, hCK, rfl⟩
  obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
  have hV : V ∈ K.faces := hCK V hVC
  have hdist : ∀ i ∈ V, ∀ j ∈ V, dist (id i) (id j) ≤ D := by
    intro i hi j hj
    exact (dist_le_diam_of_mem (isBounded_convexHull.mpr V.finite_toSet.isBounded)
      (subset_convexHull ℝ _ hi) (subset_convexHull ℝ _ hj)).trans (hK V hV)
  have h := hC.diam_convexHull_centroids_le_finrank id (K.indep hV) hCV hD hdist
  simpa only [chainCentroids, Finset.coe_image] using h

/-- Iterated geometric barycentric subdivision. -/
noncomputable def barycentricSubdivisionIter (K : Geometry.SimplicialComplex ℝ E) :
    ℕ → Geometry.SimplicialComplex ℝ E
  | 0 => K
  | n + 1 => barycentricSubdivision (barycentricSubdivisionIter K n)

@[simp] theorem barycentricSubdivisionIter_zero (K : Geometry.SimplicialComplex ℝ E) :
    barycentricSubdivisionIter K 0 = K := rfl

@[simp] theorem barycentricSubdivisionIter_succ (K : Geometry.SimplicialComplex ℝ E) (n : ℕ) :
    barycentricSubdivisionIter K (n + 1) =
      barycentricSubdivision (barycentricSubdivisionIter K n) := rfl

theorem barycentricSubdivisionIter_space (K : Geometry.SimplicialComplex ℝ E) (n : ℕ) :
    (barycentricSubdivisionIter K n).space = K.space := by
  induction n with
  | zero => rfl
  | succ n ih => rw [barycentricSubdivisionIter_succ, barycentricSubdivision_space, ih]

theorem barycentricSubdivisionIter_finite_faces (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (n : ℕ) : (barycentricSubdivisionIter K n).faces.Finite := by
  induction n with
  | zero => exact hK
  | succ n ih => exact barycentricSubdivision_finite_faces _ ih

theorem barycentricSubdivisionIter_refines (K : Geometry.SimplicialComplex ℝ E) (n : ℕ) :
    SimplicialRefines (barycentricSubdivisionIter K n) K := by
  induction n with
  | zero => exact SimplicialRefines.refl K
  | succ n ih => exact (barycentricSubdivision_refines _).trans ih

theorem barycentricSubdivisionIter_face_card_le (K : Geometry.SimplicialComplex ℝ E)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) (n : ℕ) :
    ∀ s ∈ (barycentricSubdivisionIter K n).faces, s.card ≤ d + 1 := by
  induction n with
  | zero => exact hd
  | succ n ih => exact barycentricSubdivision_face_card_le _ ih

theorem HasMeshLE.barycentricSubdivisionIter_of_face_card_le
    {K : Geometry.SimplicialComplex ℝ E} {D : ℝ} (hK : HasMeshLE K D) (hD : 0 ≤ D)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) (n : ℕ) :
    HasMeshLE (barycentricSubdivisionIter K n) (((d : ℝ) / (d + 1)) ^ n * D) := by
  induction n with
  | zero => simpa using hK
  | succ n ih =>
    have hbound := ih.barycentricSubdivision_of_face_card_le
      (mul_nonneg (pow_nonneg (by positivity) _) hD)
      (barycentricSubdivisionIter_face_card_le K hd n)
    intro s hs
    apply (hbound s hs).trans_eq
    rw [pow_succ]
    ring

/-- Arbitrarily fine subdivision preserving the original intrinsic dimension bound. -/
theorem exists_fine_subdivision_of_face_card_le
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      SimplicialRefines L K ∧
      (∀ s ∈ L.faces, diam (convexHull ℝ (s : Set E)) < ε) ∧
      ∀ s ∈ L.faces, s.card ≤ d + 1 := by
  obtain ⟨D, hD, hmesh⟩ := exists_mesh_bound K hK
  obtain ⟨N, hN⟩ := exists_barycentric_mesh_bound_lt d D hε
  refine ⟨barycentricSubdivisionIter K N, barycentricSubdivisionIter_finite_faces K hK N,
    barycentricSubdivisionIter_space K N, barycentricSubdivisionIter_refines K N, ?_,
    barycentricSubdivisionIter_face_card_le K hd N⟩
  intro s hs
  exact (hmesh.barycentricSubdivisionIter_of_face_card_le hD hd N s hs).trans_lt (hN N le_rfl)

theorem HasMeshLE.barycentricSubdivisionIter [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {D : ℝ} (hK : HasMeshLE K D) (hD : 0 ≤ D) (n : ℕ) :
    HasMeshLE (barycentricSubdivisionIter K n)
      (((Module.finrank ℝ E : ℝ) / (Module.finrank ℝ E + 1)) ^ n * D) := by
  induction n with
  | zero => simpa using hK
  | succ n ih =>
    have hbound := ih.barycentricSubdivision (mul_nonneg (pow_nonneg (by positivity) _) hD)
    intro s hs
    apply (hbound s hs).trans_eq
    rw [pow_succ]
    ring

/-- A finite geometric complex admits a finite subdivision of any prescribed positive mesh,
with the same realization and every new face contained in an original face. -/
theorem exists_fine_subdivision [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      SimplicialRefines L K ∧
      (∀ s ∈ L.faces, diam (convexHull ℝ (s : Set E)) < ε) ∧
      ∀ s ∈ L.faces, s.card ≤ Module.finrank ℝ E + 1 := by
  obtain ⟨D, hD, hmesh⟩ := exists_mesh_bound K hK
  obtain ⟨N, hN⟩ := exists_barycentric_mesh_bound_lt (Module.finrank ℝ E) D hε
  refine ⟨barycentricSubdivisionIter K N, barycentricSubdivisionIter_finite_faces K hK N,
    barycentricSubdivisionIter_space K N, barycentricSubdivisionIter_refines K N, ?_, ?_⟩
  · intro s hs
    exact (hmesh.barycentricSubdivisionIter hD N s hs).trans_lt (hN N le_rfl)
  · intro s hs
    simpa only [Fintype.card_coe] using
      ((barycentricSubdivisionIter K N).indep hs).card_le_finrank_succ.trans
        (Nat.add_le_add_right (Submodule.finrank_le _) 1)

end PoincareHighDim.Engulfing
