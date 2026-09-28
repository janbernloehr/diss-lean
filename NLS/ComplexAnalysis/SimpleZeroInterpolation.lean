import NLS.ComplexAnalysis.SimpleZeroQuotient
import NLS.ComplexAnalysis.EntireCircleDecay

/-!
# Interpolation uniqueness from a simple zero set

This is the uniqueness consequence of the dissertation's Interpolation
Lemma E.1. An entire numerator vanishing at every simple zero of an
entire product has an entire filled quotient. If that quotient tends
uniformly to zero on expanding zero-free circles, maximum modulus
forces the numerator to vanish identically.
-/

noncomputable section
open Set Filter
namespace NLS.ComplexAnalysis

theorem entire_eq_zero_of_simple_zero_interpolation
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hcommon : ∀ z, g z = 0 → f z = 0)
    (hsimple : ∀ z, g z = 0 → deriv g z ≠ 0)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hcircle : ∀ n : ℕ, ∀ z ∈ Metric.sphere (0 : ℂ) (R n), g z ≠ 0)
    (hdecay : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        ∀ z ∈ Metric.sphere (0 : ℂ) (R n), ‖f z / g z‖ ≤ ε) :
    f = 0 := by
  let H := analyticQuotient f g
  have hH : Differentiable ℂ H := by
    intro z
    exact (analyticOnNhd_analyticQuotient_of_simple_zeros
      hf hg hcommon hsimple z (mem_univ _)).differentiableAt
  exact entire_numerator_eq_zero_of_quotient_circle_decay
    f g H hH (fun z => (analyticQuotient_mul_of_simple_zeros
      hf hg hcommon z).symm)
      R hR hcircle hdecay

end NLS.ComplexAnalysis
