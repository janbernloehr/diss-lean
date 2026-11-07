import NLS.Articles.KdVPseudomeasures.OriginalHillNativeSpectralFirstVariation
import NLS.KdV.HillNativeDirichletDisplacementFirstVariation

/-! The ACTUAL original periodic midpoint and centered Dirichlet first
variations. Native complex directions include the mean; the article's
original real mean-zero directions eliminate it. Free Cartesian amplitude
and root-multiplier normalization remain separate obligations. -/
noncomputable section
open Complex NLS.KdV NLS.Fourier NLS.Fourier.SmoothPeriodicTest
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_native_midpoint_differential (n : ℕ+) (h : PeriodOneHminusOne) :
    (fderiv ℂ (hillHminusCanonicalEnergyMidpoint n) 0) h=h.val 0 :=
  fderiv_hillHminusCanonicalEnergyMidpoint_zero_apply n h

theorem original_Hill_midpoint_differential_mean_zero (n : ℕ+) (h : OriginalHminusOnePotential) :
    (fderiv ℂ (hillHminusCanonicalEnergyMidpoint n) 0) (originalPeriodOneCoefficients h)=0 := by
  rw [original_Hill_native_midpoint_differential,originalPeriodOneCoefficients_mean_zero]

theorem original_Hill_native_centered_Dirichlet_differential (n : ℕ+) (h : PeriodOneHminusOne) :
    (fderiv ℂ (fun q => hillHminusCanonicalDirichlet n q-hillHminusCanonicalEnergyMidpoint n q) 0) h =
      -(h.val (n:ℤ)+h.val (-(n:ℤ)))/2 :=
  fderiv_hillHminusDirichlet_sub_midpoint_zero_apply n h

theorem original_Hill_centered_Dirichlet_differential_even_modes (n : ℕ+)
    (h : OriginalHminusOnePotential) :
    (fderiv ℂ (fun q => hillHminusCanonicalDirichlet n q-hillHminusCanonicalEnergyMidpoint n q) 0)
        (originalPeriodOneCoefficients h) =
      -(h.val.val (mode (-(2*(n:ℤ))))+h.val.val (mode (2*(n:ℤ))))/2 := by
  rw [original_Hill_native_centered_Dirichlet_differential]
  simp only [originalPeriodOneCoefficients,periodOneOriginalExtract_apply,mul_neg,neg_neg]

theorem original_Hill_native_mean_zero_trace_stationarity (h : PeriodOneHminusOne)
    (hh : h.val 0=0) (μ : ℂ) :
    (fderiv ℂ (fun q => hillHminusDiscriminant q μ) 0) h=0 :=
  fderiv_hillHminusDiscriminant_free_mean_zero h hh μ

end NLS.Articles.KdVPseudomeasures
