import NLS.Articles.KdVPseudomeasures.OriginalHminusOneCharacteristic
import NLS.KdV.HillNativeDirichletSheetFirstVariation

/-! ACTUAL native canonical Dirichlet, norming and prescribed-sheet first
variations, with the original even Fourier labels and mean-zero source.
The Cartesian Fourier differential still needs its remaining normalization
and periodic-midpoint inputs. -/
noncomputable section
open Complex NLS.KdV NLS.Fourier NLS.Fourier.SmoothPeriodicTest
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_native_Dirichlet_differential (n : ℕ+) (h : PeriodOneHminusOne) :
    (fderiv ℂ (hillHminusCanonicalDirichlet n) 0) h =
      h.val 0-(h.val (n:ℤ)+h.val (-(n:ℤ)))/2 := by
  rw [fderiv_hillHminusCanonicalDirichlet_zero,hillFreeDirichletGradient_apply]

theorem original_Hill_native_norming_differential (n : ℕ+) (h : PeriodOneHminusOne) :
    (fderiv ℂ (hillHminusDirichletNorming n) 0) h =
      ((-1:ℂ)^(n:ℕ)/(4*I*((Real.pi:ℂ)*n)))*(h.val (-(n:ℤ))-h.val (n:ℤ)) := by
  rw [fderiv_hillHminusDirichletNorming_zero,hillFreeNormingGradient_apply]

theorem original_Hill_native_sheet_differential (n : ℕ+) (h : PeriodOneHminusOne) :
    (fderiv ℂ (hillHminusDirichletSheet n) 0) h =
      ((-1:ℂ)^(n:ℕ)/(2*I*((Real.pi:ℂ)*n)))*(h.val (n:ℤ)-h.val (-(n:ℤ))) :=
  fderiv_hillHminusDirichletSheet_zero_apply n h

theorem originalPeriodOneCoefficients_mean_zero (h : OriginalHminusOnePotential) :
    (originalPeriodOneCoefficients h).val 0 = 0 := by
  rw [originalPeriodOneCoefficients,periodOneOriginalExtract_apply]
  simpa only [mul_zero,neg_zero] using h.property.2.1

theorem original_Hill_Dirichlet_differential_even_modes (n : ℕ+) (h : OriginalHminusOnePotential) :
    (fderiv ℂ (hillHminusCanonicalDirichlet n) 0) (originalPeriodOneCoefficients h) =
      -(h.val.val (mode (-(2*(n:ℤ))))+h.val.val (mode (2*(n:ℤ))))/2 := by
  rw [original_Hill_native_Dirichlet_differential,originalPeriodOneCoefficients_mean_zero]
  simp only [originalPeriodOneCoefficients,periodOneOriginalExtract_apply,mul_neg,neg_neg,zero_sub,neg_div]

theorem original_Hill_norming_differential_even_modes (n : ℕ+) (h : OriginalHminusOnePotential) :
    (fderiv ℂ (hillHminusDirichletNorming n) 0) (originalPeriodOneCoefficients h) =
      ((-1:ℂ)^(n:ℕ)/(4*I*((Real.pi:ℂ)*n)))*
        (h.val.val (mode (2*(n:ℤ)))-h.val.val (mode (-(2*(n:ℤ))))) := by
  rw [original_Hill_native_norming_differential]
  simp only [originalPeriodOneCoefficients,periodOneOriginalExtract_apply,mul_neg,neg_neg]

end NLS.Articles.KdVPseudomeasures
