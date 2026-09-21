import NLS.SequenceSpaces.ExponentEmbedding
import NLS.Fourier.HalfIntervalBoundedness

/-!
# Half-interval Fourier coefficients across exponents
The physical finite-polynomial formula does not depend on the sequence
exponent. Density and continuity identify the completed maps as well.
-/

noncomputable section
open scoped ENNReal
namespace NLS
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Finite coefficients are unchanged by the exponent inclusion. -/
@[simp] theorem Coeff.exponentInclusion_ofFinsupp (h : p ≤ q) (a : ℤ →₀ ℂ) :
    Coeff.exponentInclusion h (Coeff.ofFinsupp a) = Coeff.ofFinsupp a := by
  ext n
  rfl

namespace Fourier

/-- Physical half-interval coefficients of a finite polynomial are exponent independent. -/
theorem polynomialHalfCoeffs_exponent (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q)
    (a : ℤ →₀ ℂ) :
    Coeff.exponentInclusion h (polynomialHalfCoeffs hp1 a) = polynomialHalfCoeffs hq1 a := by
  ext n
  simp only [Coeff.exponentInclusion_apply, polynomialHalfCoeffs_apply]

/-- The completed half-interval map commutes with every finite exponent inclusion. -/
theorem halfIntervalCoeffs_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (a : Coeff p) :
    Coeff.exponentInclusion h (halfIntervalCoeffs hp1 hp a) =
      halfIntervalCoeffs hq1 hq (Coeff.exponentInclusion h a) := by
  have he : (fun a : Coeff p => Coeff.exponentInclusion h (halfIntervalCoeffs hp1 hp a)) =
      (fun a => halfIntervalCoeffs hq1 hq (Coeff.exponentInclusion h a)) := by
    apply (Coeff.denseRange_ofFinsupp hp).equalizer
      ((Coeff.exponentInclusion h).continuous.comp (halfIntervalCoeffs hp1 hp).continuous)
      ((halfIntervalCoeffs hq1 hq).continuous.comp (Coeff.exponentInclusion h).continuous)
    funext a
    simp only [Function.comp_apply]
    rw [Coeff.exponentInclusion_ofFinsupp, halfIntervalCoeffs_finite, halfIntervalCoeffs_finite,
      polynomialHalfCoeffs_exponent]
  exact congrFun he a

end Fourier
end NLS
