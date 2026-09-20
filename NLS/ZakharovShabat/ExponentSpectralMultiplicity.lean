import NLS.ZakharovShabat.ExponentRootSpaces
import NLS.ZakharovShabat.ParityRootMultiplicity

/-!
# Spectrum and parity multiplicity across finite exponents

The exact root-space comparison preserves every Fourier parity. Both the
full spectrum and the original parity algebraic multiplicities are therefore
independent of increasing the ambient exponent of a fixed potential.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Exponent inclusion maps each full parity root space onto its counterpart. -/
theorem parityRootSpace_map_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (z : ℂ) (k : ℤ) :
    (periodicRootSpaceTop hp φ z ⊓ pairParitySubspace k).map (pairExponentInclusion h).toLinearMap =
      periodicRootSpaceTop hq (pairExponentInclusion h φ) z ⊓ pairParitySubspace k := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hpar⟩, rfl⟩
    refine ⟨?_, (pairExponentInclusion_mem_parity_iff h y k).mpr hpar⟩
    rw [← periodicRootSpaceTop_map_exponent hp hq h]
    exact ⟨y, hy, rfl⟩
  · rintro ⟨hx, hpar⟩
    rw [← periodicRootSpaceTop_map_exponent hp hq h] at hx
    obtain ⟨y, hy, he⟩ := hx
    refine ⟨y, ⟨hy, ?_⟩, he⟩
    apply (pairExponentInclusion_mem_parity_iff h y k).mp
    exact he ▸ hpar

/-- Both original parity algebraic multiplicities are unchanged by exponent inclusion. -/
theorem parityAlgebraicMultiplicity_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (z : ℂ) (k : ℤ) :
    parityAlgebraicMultiplicity hp φ k z =
      parityAlgebraicMultiplicity hq (pairExponentInclusion h φ) k z := by
  simp only [parityAlgebraicMultiplicity]
  rw [← parityRootSpace_map_exponent hp hq h]
  exact (Submodule.equivMapOfInjective (pairExponentInclusion h).toLinearMap
    (pairExponentInclusion_injective h) _).finrank_eq

/-- The full original periodic spectrum is independent of increasing the exponent. -/
theorem periodicSpectrum_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q) (φ : PairSpace p) :
    periodicSpectrum hp φ = periodicSpectrum hq (pairExponentInclusion h φ) := by
  ext z
  rw [← periodicAlgebraicMultiplicity_pos_iff hp φ,
    ← periodicAlgebraicMultiplicity_pos_iff hq (pairExponentInclusion h φ),
    periodicAlgebraicMultiplicity_exponent hp hq h]

end NLS.ZakharovShabat
