import NLS.ComplexAnalysis.ZeroCountComparison

/-! # Powers and natural analytic zero counts -/
noncomputable section
namespace NLS.ComplexAnalysis

/-- Taking a power multiplies the natural-order count. Nonvanishing boundary hypotheses in applications ensure these are genuine finite zero counts. -/
theorem analyticZeroCount_pow (f : ℂ → ℂ) (K : Set ℂ)
    (hf : AnalyticOnNhd ℂ f K) (m : ℕ) :
    analyticZeroCount (fun z => f z ^ m) K = m * analyticZeroCount f K := by
  classical
  unfold analyticZeroCount
  calc
    _ = ∑ᶠ z : ℂ, m * (if z ∈ K then analyticOrderNatAt f z else 0) := by
      apply finsum_congr
      intro z
      by_cases hz : z ∈ K
      · simp only [if_pos hz]
        exact analyticOrderNatAt_pow (hf z hz) m
      · simp only [if_neg hz, mul_zero]
    _ = _ := (mul_finsum _ _).symm

end NLS.ComplexAnalysis
