import NLS.ZakharovShabat.ExponentSpectralMultiplicity
import NLS.ZakharovShabat.CanonicalDiscriminant

/-!
# Canonical products are compatible across finite sequence exponents

Equality of the original spectrum and parity multiplicities identifies every
central polynomial before taking any limit. The intrinsic full and parity
products, and the intrinsic discriminant, therefore agree under inclusion.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Every fixed central spectral set is unchanged by exponent inclusion. -/
theorem centralPeriodicSpectrum_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (N : ℕ) :
    centralPeriodicSpectrum hp φ N = centralPeriodicSpectrum hq (pairExponentInclusion h φ) N := by
  ext z
  simp only [mem_centralPeriodicSpectrum, periodicSpectrum_exponent hp hq h]

/-- The full central spectral polynomial is independent of the ambient exponent. -/
theorem centralPeriodicPolynomial_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (N : ℕ) (z : ℂ) :
    centralPeriodicPolynomial hp φ N z = centralPeriodicPolynomial hq (pairExponentInclusion h φ) N z := by
  simp only [centralPeriodicPolynomial, centralPeriodicSpectrum_exponent hp hq h,
    periodicAlgebraicMultiplicity_exponent hp hq h]

/-- Both central parity polynomials retain exactly the same root multiplicities. -/
theorem centralParityPolynomial_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (N : ℕ) (k : ℤ) (z : ℂ) :
    centralParityPolynomial hp φ N k z = centralParityPolynomial hq (pairExponentInclusion h φ) N k z := by
  simp only [centralParityPolynomial, centralPeriodicSpectrum_exponent hp hq h,
    parityAlgebraicMultiplicity_exponent hp hq h]

/-- Every normalized full approximant is already compatible across exponents. -/
theorem normalizedCentralPeriodicPolynomial_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (N : ℕ) (z : ℂ) :
    normalizedCentralPeriodicPolynomial hp φ N z =
      normalizedCentralPeriodicPolynomial hq (pairExponentInclusion h φ) N z := by
  simp only [normalizedCentralPeriodicPolynomial, centralPeriodicPolynomial_exponent hp hq h]

/-- The corrected parity normalizations commute with exponent inclusion. -/
theorem normalizedCentralParityPolynomial_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (N : ℕ) (k : ℤ) (z : ℂ) :
    normalizedCentralParityPolynomial hp φ N k z =
      normalizedCentralParityPolynomial hq (pairExponentInclusion h φ) N k z := by
  simp only [normalizedCentralParityPolynomial, centralParityPolynomial_exponent hp hq h]

/-- The intrinsic full product is independent of increasing the exponent. -/
theorem canonicalPeriodicProduct_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (z : ℂ) :
    canonicalPeriodicProduct hp φ z = canonicalPeriodicProduct hq (pairExponentInclusion h φ) z := by
  simp only [canonicalPeriodicProduct, normalizedCentralPeriodicPolynomial_exponent hp hq h]

/-- The intrinsic parity products are independent of increasing the exponent. -/
theorem canonicalParityProduct_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (k : ℤ) (z : ℂ) :
    canonicalParityProduct hp φ k z = canonicalParityProduct hq (pairExponentInclusion h φ) k z := by
  simp only [canonicalParityProduct, normalizedCentralParityPolynomial_exponent hp hq h]

/-- The intrinsic discriminant represents the same function in every larger finite exponent. -/
theorem canonicalDiscriminant_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (z : ℂ) :
    canonicalDiscriminant hp φ z = canonicalDiscriminant hq (pairExponentInclusion h φ) z := by
  simp only [canonicalDiscriminant, canonicalParityProduct_exponent hp hq h]

end NLS.ZakharovShabat
