import Submission.Morse.Defs
import Submission.DifferentialGeometry.Topology.Morse.NoCriticalValues

/-!
# The regular interval theorem

Milnor, *Lectures on the h-cobordism theorem*, Theorem 3.4 in strip form: if the compact strip
`f ⁻¹' (Set.Icc a b)` contains no critical point, then a diffeomorphism of `M` carries the
sublevel set at `a` onto the sublevel set at `b` and the level set at `a` onto the level set
at `b`.

This is proved in the dependency: `DifferentialGeometry.Topology.Morse.no_critical_value_transport`
returns the diffeomorphism together with the sublevel-set identity and the pointwise facts
`f x = a → f (Φ x) = b` and `f x = b → f (Φ.symm x) = a`, which give the level-set identity.
The dependency's flow theory is vendored under `Submission/DifferentialGeometry/` (see the
license notice there), with its statements generalised from analytic to smooth atlases and from
`Type` to `Type*`.
-/

namespace PoincareHighDim

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **Regular interval theorem** (Milnor, Theorem 3.4, strip form). -/
theorem regular_interval (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x ∈ f ⁻¹' Icc a b, ¬ IsCriticalPt I f x) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, Φ '' (f ⁻¹' Iic a) = f ⁻¹' Iic b ∧ Φ '' (f ⁻¹' {a}) = f ⁻¹' {b} := by
  -- The transport theorem of the dependency provides the diffeomorphism together with the
  -- sublevel-set transport and the pointwise behaviour on the level sets `f = a` and `f = b`.
  obtain ⟨v, Φ, -, -, -, -, ⟨-, hflow, -⟩, hbnd, -, hbnd', -⟩ :=
    DifferentialGeometry.Topology.Morse.no_critical_value_transport (I := I) f hf hab hcompact
      (fun x hx => hreg x hx)
  refine ⟨Φ, hflow, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hbnd x hx
  · intro hy
    exact ⟨Φ.symm y, hbnd' y hy, Φ.apply_symm_apply y⟩

end PoincareHighDim
