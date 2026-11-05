import NLS.KdV.MiuraHillPsiNumerators
import NLS.ZakharovShabat.SourcePsiOddGrowth

/-! Actual energy-numerator growth, separated from global divisor labels. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat
namespace NLS.KdV.MiuraHillPsiFamily

theorem numerator_pullback_sub_sine_growth (A : MiuraHillPsiFamily) (n : ℕ+) (u : Coeff 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖(2*z*A.numerator n (z^2,u))/(-2*sin z)‖ ≤ ε := by
  have h := sourceOddPsiCandidate_sub_sine_growth (by norm_num) (by norm_num) ((n:ℕ):ℤ)
    (A.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u):Coeff 2) ε hε
  simpa only [sourceOddPsiCandidate,← A.numerator_frequency_identity n u] using h

end NLS.KdV.MiuraHillPsiFamily
