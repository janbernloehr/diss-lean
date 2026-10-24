import NLS.FunctionalAnalysis.RealPoissonKernel
import NLS.ZakharovShabat.L2WholeLineSpectralResolventIntegral

/-! # Poisson integrals for the original physical spectral measures -/
noncomputable section
set_option autoImplicit false
open MeasureTheory NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The Poisson transform of the actual real measure is the negative imaginary
part of the original physical resolvent expectation. -/
theorem wholeLineRealSpectralMeasure_poisson_integral (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2)
    (x ε : ℝ) (hε : 0 < ε) :
    ∫ t, realPoissonKernel x ε t ∂wholeLineRealSpectralMeasure u hu v =
      -(inner ℂ v (wholeLineNonrealResolvent u hu ((x : ℂ)+(ε : ℂ)*Complex.I)
        (by simpa using ne_of_gt hε) v)).im := by
  rw [integral_realPoissonKernel_eq_neg_im _ x ε hε,
    wholeLineRealSpectralMeasure_resolvent_integral u hu v _ (by simpa using ne_of_gt hε)]

/-- The actual physical measure of a centered interval is bounded by its resolvent. -/
theorem wholeLineRealSpectralMeasure_Icc_le_resolvent (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2)
    (x ε : ℝ) (hε : 0 < ε) :
    (wholeLineRealSpectralMeasure u hu v).real (Set.Icc (x-ε) (x+ε)) ≤
      2*ε*(-(inner ℂ v (wholeLineNonrealResolvent u hu ((x : ℂ)+(ε : ℂ)*Complex.I)
        (by simpa using ne_of_gt hε) v)).im) := by
  rw [← wholeLineRealSpectralMeasure_poisson_integral u hu v x ε hε]
  exact measureReal_Icc_le_poisson_integral _ x ε hε

/-- A bound on the original resolvent expectation gives an interval mass bound. -/
theorem wholeLineRealSpectralMeasure_Icc_le_of_resolvent_bound (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2)
    (x ε C : ℝ) (hε : 0 < ε)
    (hC : ‖inner ℂ v (wholeLineNonrealResolvent u hu ((x : ℂ)+(ε : ℂ)*Complex.I)
      (by simpa using ne_of_gt hε) v)‖ ≤ C) :
    (wholeLineRealSpectralMeasure u hu v).real (Set.Icc (x-ε) (x+ε)) ≤ 2*ε*C := by
  apply measureReal_Icc_le_of_poisson_bound _ x ε C hε
  rw [wholeLineRealSpectralMeasure_poisson_integral u hu v x ε hε]
  exact (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans hC)

end NLS.ZakharovShabat
