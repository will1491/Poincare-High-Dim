import Submission.Topology.Cellular
import Submission.Topology.RestoreFiber
import Submission.Topology.SaturatedImage
import Submission.Topology.SphereCompression

/-!
# Cell neighborhoods of a collapsed fiber

Conjugating a compression through a map with one collapsed fiber, and restoring that fiber
pointwise, produces smaller embedded cells. The openness hypothesis on the image of the
open disk replaces any use of invariance of domain.
-/

namespace PoincareHighDim

open Set Metric Topology

section Restore

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : Disk n → Y} {K U : Set (Disk n)}

/-- Restoring a fiber after compressing the image yields a closed-cell neighborhood of it. -/
theorem exists_closedCell_of_restored_compression (hf : Continuous f)
    (hfK : CollapsesExactly f K) (hKI : K ⊆ diskInterior n)
    (hfI : IsOpen (f '' diskInterior n)) (hKU : K ⊆ U)
    (h : Y ≃ₜ Y) (hmove : h '' range f ⊆ f '' U)
    {V : Set Y} (hV : IsOpen V) (hKV : f '' K ⊆ V)
    (hfix : ∀ y ∈ V, h y = y) :
    ∃ c : ClosedCell n (Disk n), K ⊆ c.interiorSet ∧ c.carrier ⊆ U := by
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  obtain ⟨g, hg, hgf, hgfix, -, hgrange⟩ := exists_closedEmbedding_restoreFiber hf hfK h
    hV hKV hfix (hmove.trans (image_subset_range f U))
  have hI : g '' diskInterior n = f ⁻¹' (h '' (f '' diskInterior n)) :=
    image_of_restored_range hfK hKI h hgf hgrange
  let c : ClosedCell n (Disk n) := {
    map := g
    isClosedEmbedding := hg
    isOpen_interior := by rw [hI]; exact (h.isOpenMap _ hfI).preimage hf }
  refine ⟨c, ?_, ?_⟩
  · intro x hx
    exact ⟨x, hKI hx, hgfix x (hKV ⟨x, hx, rfl⟩)⟩
  · intro x hx
    have hx' : f x ∈ h '' range f := by
      change x ∈ range g at hx
      rwa [hgrange] at hx
    have : x ∈ f ⁻¹' (f '' U) := hmove hx'
    rwa [hfK.preimage_image_eq_of_subset hKU] at this

end Restore

namespace ClosedCell

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

/-- An open subset of the disk lying in its open interior has open image in the ambient
space under a closed-cell parametrization. -/
theorem isOpen_image_of_subset_interior (c : ClosedCell n X) {U : Set (Disk n)}
    (hU : IsOpen U) (hUI : U ⊆ diskInterior n) : IsOpen (c.map '' U) := by
  obtain ⟨V, hV, heq⟩ := c.isClosedEmbedding.isEmbedding.isInducing.image_eq_isOpen_inter_range hU
  have hsub : c.map '' U ⊆ c.interiorSet := image_mono hUI
  have himage : c.map '' U = V ∩ c.interiorSet := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨(heq ▸ hx).1, hsub hx⟩
    · intro x hx
      rw [heq]
      exact ⟨hx.1, c.interiorSet_subset_carrier hx.2⟩
  rw [himage]
  exact hV.inter c.isOpen_interior

/-- A cell contained in the open disk can be inserted into any ambient cell. -/
def nest (c : ClosedCell n X) (d : ClosedCell n (Disk n))
    (hd : d.carrier ⊆ diskInterior n) : ClosedCell n X where
  map := c.map ∘ d.map
  isClosedEmbedding := c.isClosedEmbedding.comp d.isClosedEmbedding
  isOpen_interior := by
    rw [image_comp]
    exact c.isOpen_image_of_subset_interior d.isOpen_interior
      (d.interiorSet_subset_carrier.trans hd)

@[simp]
theorem nest_carrier (c : ClosedCell n X) (d : ClosedCell n (Disk n))
    (hd : d.carrier ⊆ diskInterior n) : (c.nest d hd).carrier = c.map '' d.carrier :=
  range_comp c.map d.map

@[simp]
theorem nest_interiorSet (c : ClosedCell n X) (d : ClosedCell n (Disk n))
    (hd : d.carrier ⊆ diskInterior n) : (c.nest d hd).interiorSet = c.map '' d.interiorSet :=
  image_comp c.map d.map (diskInterior n)

end ClosedCell

section Sphere

variable {n : ℕ} {f : Disk n → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}
    {K : Set (Disk n)}

/-- A proper sphere-valued map of a disk with one collapsed fiber gives arbitrarily small
cell neighborhoods of that fiber. Each new cell lies in the original open disk. -/
theorem exists_cell_neighborhood_of_collapsesExactly_sphere
    (hf : Continuous f) (hfK : CollapsesExactly f K) (hKne : K.Nonempty)
    (hKI : K ⊆ diskInterior n) (hproper : range f ≠ univ)
    (hfI : IsOpen (f '' diskInterior n))
    (U : Set (Disk n)) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ c : ClosedCell n (Disk n), K ⊆ c.interiorSet ∧
      c.carrier ⊆ U ∩ diskInterior n := by
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let W := U ∩ diskInterior n
  have hKW : K ⊆ W := subset_inter hKU hKI
  have hW : IsOpen W := hU.inter (isOpen_diskInterior n)
  have hfW : IsOpen (f '' W) := isOpen_image_of_saturated hf hW hfI
    (image_mono inter_subset_right) (image_subset_range _ _) (by
      intro x y hxy hx
      rcases (hfK x y).mp hxy with rfl | ⟨-, hy⟩
      · exact hx
      · exact hKW hy)
  obtain ⟨x, hx⟩ := hKne
  obtain ⟨h, hmove, V, hV, haV, hfix⟩ := exists_sphere_compression
    (isCompact_range hf) hproper (mem_range_self x) hfW ⟨x, hKW hx, rfl⟩
  have hKV : f '' K ⊆ V := by
    rintro y ⟨z, hz, rfl⟩
    have heq : f z = f x := (hfK z x).mpr (Or.inr ⟨hz, hx⟩)
    rwa [heq]
  exact exists_closedCell_of_restored_compression hf hfK hKI hfI hKW h hmove hV hKV hfix

/-- **One-fiber cellularity.** A compact exceptional fiber in the interior of a disk is
cellular if collapsing it embeds the quotient in the sphere with open interior image. -/
theorem isCellular_of_collapsesExactly_sphere
    (hf : Continuous f) (hfK : CollapsesExactly f K) (hK : IsCompact K)
    (hKne : K.Nonempty) (hKI : K ⊆ diskInterior n) (hproper : range f ≠ univ)
    (hfI : IsOpen (f '' diskInterior n)) : IsCellular n K := by
  apply isCellular_of_cell_neighborhoods hK.isClosed hKne
  intro U hU hKU
  obtain ⟨c, hKc, hcU⟩ := exists_cell_neighborhood_of_collapsesExactly_sphere
    hf hfK hKne hKI hproper hfI U hU hKU
  exact ⟨c, hKc, hcU.trans inter_subset_left⟩

/-- The one-fiber criterion also proves cellularity in an ambient space containing the
original disk as a closed cell. -/
theorem ClosedCell.isCellular_image_of_collapsesExactly_sphere
    {X : Type*} [MetricSpace X] (c : ClosedCell n X)
    (hf : Continuous f) (hfK : CollapsesExactly f K) (hK : IsCompact K)
    (hKne : K.Nonempty) (hKI : K ⊆ diskInterior n) (hproper : range f ≠ univ)
    (hfI : IsOpen (f '' diskInterior n)) : IsCellular n (c.map '' K) := by
  apply isCellular_of_cell_neighborhoods
    (hK.image c.isClosedEmbedding.continuous).isClosed (hKne.image c.map)
  intro U hU hKU
  have hKpre : K ⊆ c.map ⁻¹' U := fun x hx => hKU ⟨x, hx, rfl⟩
  obtain ⟨d, hKd, hd⟩ := exists_cell_neighborhood_of_collapsesExactly_sphere
    hf hfK hKne hKI hproper hfI (c.map ⁻¹' U)
    (hU.preimage c.isClosedEmbedding.continuous) hKpre
  refine ⟨c.nest d (hd.trans inter_subset_right), ?_, ?_⟩
  · rw [ClosedCell.nest_interiorSet]
    exact image_mono hKd
  · rw [ClosedCell.nest_carrier]
    rintro x ⟨y, hy, rfl⟩
    exact (hd hy).1

end Sphere

end PoincareHighDim
