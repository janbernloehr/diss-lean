import NLS.Fourier.DistributionDerivative
import NLS.SequenceSpaces.PeriodDoubling

/-! # Actual distribution derivatives in the period-one coefficient convention -/
noncomputable section
open scoped SchwartzMap FourierTransform
namespace NLS.Fourier

/-- The actual period-one tempered distribution of an original L² field. -/
def periodOneL2Distribution : Coeff 2 →L[ℂ] 𝓢'(ℝ, ℂ) :=
  distributionSynthesisCLM.comp Coeff.periodDouble.toContinuousLinearMap

theorem periodOneL2Distribution_derivative_eq (a b : Coeff 2)
    (h : ∀ j : ℤ, b j = 2*Complex.I*(Real.pi : ℂ)*j*a j) :
    TemperedDistribution.derivCLM ℂ (periodOneL2Distribution a) = periodOneL2Distribution b := by
  apply (distributionDerivative_eq_iff (Coeff.periodDouble a) (Coeff.periodDouble b)).mpr
  intro n
  by_cases hn : n%2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he, Coeff.periodDouble_even, Coeff.periodDouble_even, h]
    push_cast
    ring
  · have he : n = 2*(n/2)+1 := by omega
    rw [he, Coeff.periodDouble_odd, Coeff.periodDouble_odd, mul_zero]

end NLS.Fourier
