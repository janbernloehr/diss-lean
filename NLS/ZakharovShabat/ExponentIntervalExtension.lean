import NLS.Fourier.ExponentHalfInterval
import NLS.ZakharovShabat.ExponentInclusions
import NLS.ZakharovShabat.BoundedIntervalExtension

/-!
# Reflected interval extensions across finite exponents
The boundary amplitudes are sums of half-interval coefficients and their
signed reflections. Their completed maps therefore commute with exponent
inclusion for both ordinary and auxiliary potential extensions.
-/

noncomputable section
open NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (b : BoundaryCondition)

/-- The completed boundary amplitude commutes with coefficient inclusion. -/
theorem intervalAmplitudeCLM_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (a : PairSpace p) :
    Coeff.exponentInclusion h (b.intervalAmplitudeCLM hp1 hp a) =
      b.intervalAmplitudeCLM hq1 hq (pairExponentInclusion h a) := by
  ext n
  change halfIntervalCoeffs hp1 hp a.2 n + extensionSign b * halfIntervalCoeffs hp1 hp a.1 (-n) =
    halfIntervalCoeffs hq1 hq (Coeff.exponentInclusion h a.2) n +
      extensionSign b * halfIntervalCoeffs hq1 hq (Coeff.exponentInclusion h a.1) (-n)
  rw [← halfIntervalCoeffs_exponent hp hq hp1 hq1 h a.2,
    ← halfIntervalCoeffs_exponent hp hq hp1 hq1 h a.1]
  rfl

/-- The complete reflected potential extension commutes with exponent inclusion. -/
theorem intervalExtensionCLM_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (a : PairSpace p) :
    pairExponentInclusion h (b.intervalExtensionCLM hp1 hp a) =
      b.intervalExtensionCLM hq1 hq (pairExponentInclusion h a) := by
  apply Prod.ext
  · ext n
    change extensionSign b * b.intervalAmplitudeCLM hp1 hp a (-n) =
      extensionSign b * b.intervalAmplitudeCLM hq1 hq (pairExponentInclusion h a) (-n)
    rw [← b.intervalAmplitudeCLM_exponent hp hq hp1 hq1 h a]
    rfl
  · exact b.intervalAmplitudeCLM_exponent hp hq hp1 hq1 h a

end NLS.ZakharovShabat.BoundaryCondition
