import NLS.ZakharovShabat.ExponentRootSpaces
import NLS.ZakharovShabat.BoundaryRootSpaces

/-!
# Boundary spectra and multiplicities across finite exponents
Coefficient inclusion preserves both reflection conditions. Intersecting the
exact periodic root-space comparison with these conditions transports all
boundary generalized eigenvectors and their original algebraic multiplicities.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Exponent inclusion preserves and reflects either boundary condition. -/
@[simp] theorem pairExponentInclusion_mem_boundary_iff (h : p ≤ q)
    (x : PairSpace p) (b : BoundaryCondition) :
    pairExponentInclusion h x ∈ b.space ↔ x ∈ b.space := by
  cases b <;> simp only [BoundaryCondition.space, mem_dirichletSubspace,
    mem_neumannSubspace, pairExponentInclusion_apply, Coeff.exponentInclusion_apply]

/-- The weighted domain inclusion preserves and reflects either boundary condition. -/
@[simp] theorem domainExponentInclusion_mem_boundary_iff (h : p ≤ q)
    (x : Domain p) (b : BoundaryCondition) :
    domainExponentInclusion h x ∈ b.domain ↔ x ∈ b.domain := by
  rw [← b.inclusion_mem, domainInclusion_domainExponentInclusion,
    pairExponentInclusion_mem_boundary_iff, b.inclusion_mem]

namespace BoundaryCondition
variable (b : BoundaryCondition)

/-- Every finite boundary part of a periodic root chain is transported exactly. -/
theorem periodicRootSpace_inf_map_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (z : ℂ) (n : ℕ) :
    (periodicRootSpace hp φ z n ⊓ b.space).map (pairExponentInclusion h).toLinearMap =
      periodicRootSpace hq (pairExponentInclusion h φ) z n ⊓ b.space := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hb⟩, rfl⟩
    refine ⟨?_, (pairExponentInclusion_mem_boundary_iff h y b).mpr hb⟩
    rw [← periodicRootSpace_map_exponent hp hq h]
    exact ⟨y, hy, rfl⟩
  · rintro ⟨hx, hb⟩
    rw [← periodicRootSpace_map_exponent hp hq h] at hx
    obtain ⟨y, hy, he⟩ := hx
    exact ⟨y, ⟨hy, (pairExponentInclusion_mem_boundary_iff h y b).mp (he ▸ hb)⟩, he⟩

/-- The full boundary part of the periodic root space is transported exactly. -/
theorem periodicRootSpaceTop_inf_map_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (z : ℂ) :
    (periodicRootSpaceTop hp φ z ⊓ b.space).map (pairExponentInclusion h).toLinearMap =
      periodicRootSpaceTop hq (pairExponentInclusion h φ) z ⊓ b.space := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hb⟩, rfl⟩
    refine ⟨?_, (pairExponentInclusion_mem_boundary_iff h y b).mpr hb⟩
    rw [← periodicRootSpaceTop_map_exponent hp hq h]
    exact ⟨y, hy, rfl⟩
  · rintro ⟨hx, hb⟩
    rw [← periodicRootSpaceTop_map_exponent hp hq h] at hx
    obtain ⟨y, hy, he⟩ := hx
    exact ⟨y, ⟨hy, (pairExponentInclusion_mem_boundary_iff h y b).mp (he ▸ hb)⟩, he⟩

/-- Original boundary algebraic multiplicities are independent of increasing the exponent. -/
theorem algebraicMultiplicity_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (hψ : pairExponentInclusion h φ ∈ dirichletSubspace) (z : ℂ) :
    b.algebraicMultiplicity hp φ hφ z =
      b.algebraicMultiplicity hq (pairExponentInclusion h φ) hψ z := by
  rw [← b.finrank_periodicRootSpaceTop_inf hp φ hφ z,
    ← b.finrank_periodicRootSpaceTop_inf hq (pairExponentInclusion h φ) hψ z,
    ← b.periodicRootSpaceTop_inf_map_exponent hp hq h]
  exact (Submodule.equivMapOfInjective (pairExponentInclusion h).toLinearMap
    (pairExponentInclusion_injective h) _).finrank_eq

/-- The actual boundary spectrum is unchanged by increasing the ambient finite exponent. -/
theorem spectrum_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (hψ : pairExponentInclusion h φ ∈ dirichletSubspace) :
    b.spectrum hp φ hφ = b.spectrum hq (pairExponentInclusion h φ) hψ := by
  ext z
  rw [← b.algebraicMultiplicity_pos_iff hp φ hφ,
    ← b.algebraicMultiplicity_pos_iff hq (pairExponentInclusion h φ) hψ,
    b.algebraicMultiplicity_exponent hp hq h φ hφ hψ]

end BoundaryCondition
end NLS.ZakharovShabat
