import NLS.Articles.KdVPseudomeasures.OriginalHillNativeSpectralFirstVariation
import NLS.KdV.HillNativeComplexLocalInverse

/-! Actual signed complex coordinates with original sqrt-two convention,
exact original even-mode Fourier derivative, and analytic local inversion
on the correct complex mean-zero Banach source. Main theorems remain open. -/
noncomputable section
open Complex Filter Topology NLS.KdV NLS.Fourier NLS.Fourier.SmoothPeriodicTest
namespace NLS.Articles.KdVPseudomeasures

def originalHillSignedComplexCoordinates (q : OriginalHminusOnePotential) : HillSignedComplexTarget :=
  hillMeanZeroComplexMap ⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_mean_zero q⟩

theorem original_Hill_signed_complex_domain_contains_real_source (q : OriginalHminusOnePotential) :
    (⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_mean_zero q⟩ : HillMeanZeroSource) ∈
      hillMeanZeroComplexDomain :=
  real_mem_hillMeanZeroComplexDomain _ (originalPeriodOneCoefficients_real q)

theorem original_Hill_signed_complex_coordinates (q : OriginalHminusOnePotential) (n : ℕ+) :
    (originalHillSignedComplexCoordinates q).val.val ((n:ℕ):ℤ)=
      hillHminusActionAngleFactorMinus n (originalPeriodOneCoefficients q)/(Real.sqrt 2:ℂ) ∧
    (originalHillSignedComplexCoordinates q).val.val (-((n:ℕ):ℤ))=
      hillHminusActionAngleFactorPlus n (originalPeriodOneCoefficients q)/(Real.sqrt 2:ℂ) := by
  have hq := real_mem_hillHminusActionAngleNativeDomain _ (originalPeriodOneCoefficients_real q)
  have he := hillMeanZeroComplexMap_coe
    ⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_mean_zero q⟩
  constructor
  · change (hillMeanZeroComplexMap _).val.val _=_
    rw [he]
    exact hillHminusNativeComplexMap_positive _ hq n
  · change (hillMeanZeroComplexMap _).val.val _=_
    rw [he]
    exact hillHminusNativeComplexMap_negative _ hq n

theorem original_Hill_signed_complex_action (q : OriginalHminusOnePotential) (n : ℕ+) :
    (originalHillSignedComplexCoordinates q).val.val ((n:ℕ):ℤ)*
      (originalHillSignedComplexCoordinates q).val.val (-((n:ℕ):ℤ))=
        hillHminusCanonicalAction n (originalPeriodOneCoefficients q) := by
  change (hillMeanZeroComplexMap _).val.val _*(hillMeanZeroComplexMap _).val.val _=_
  rw [hillMeanZeroComplexMap_coe]
  exact hillHminusNativeComplexMap_action_identity _
    (real_mem_hillHminusActionAngleNativeDomain _ (originalPeriodOneCoefficients_real q)) n


theorem original_Hill_signed_real_form (q : OriginalHminusOnePotential) (k : ℤ) :
    (originalHillSignedComplexCoordinates q).val.val (-k)=
      (starRingEnd ℂ) ((originalHillSignedComplexCoordinates q).val.val k) := by
  change (hillMeanZeroComplexMap _).val.val (-k)=(starRingEnd ℂ) ((hillMeanZeroComplexMap _).val.val k)
  rw [hillMeanZeroComplexMap_coe]
  exact hillHminusNativeComplexMap_real _ (originalPeriodOneCoefficients_real q) k

theorem original_Hill_signed_Fourier_differential_even_modes (n : ℕ+) (h : OriginalHminusOnePotential) :
    ((fderiv ℂ hillHminusNativeComplexMap 0) (originalPeriodOneCoefficients h)).val ((n:ℕ):ℤ)=
      h.val.val (mode (-(2*(n:ℤ))))/(Real.sqrt (2*Real.pi*(n:ℕ)):ℂ) ∧
    ((fderiv ℂ hillHminusNativeComplexMap 0) (originalPeriodOneCoefficients h)).val (-((n:ℕ):ℤ))=
      h.val.val (mode (2*(n:ℤ)))/(Real.sqrt (2*Real.pi*(n:ℕ)):ℂ) := by
  rw [fderiv_hillHminusNativeComplexMap_positive_mean_zero n _ (originalPeriodOneCoefficients_mean_zero h),
    fderiv_hillHminusNativeComplexMap_negative_mean_zero n _ (originalPeriodOneCoefficients_mean_zero h)]
  simp only [originalPeriodOneCoefficients,periodOneOriginalExtract_apply,mul_neg,neg_neg,and_self]

theorem original_Hill_signed_mean_zero_derivative_equiv :
    fderiv ℂ hillMeanZeroComplexMap 0=(WeightedCoeff.meanZeroHalfFourierEquiv 2).toContinuousLinearMap :=
  fderiv_hillMeanZeroComplexMap_zero

theorem original_Hill_signed_analytic_localInverse :
    ∃ g : HillSignedComplexTarget → HillMeanZeroSource, AnalyticAt ℂ g 0 ∧ g 0=0 ∧
      (∀ᶠ q in 𝓝 (0 : HillMeanZeroSource), g (hillMeanZeroComplexMap q)=q) ∧
      (∀ᶠ z in 𝓝 (0 : HillSignedComplexTarget), hillMeanZeroComplexMap (g z)=z) ∧
      fderiv ℂ g 0=(WeightedCoeff.meanZeroHalfFourierEquiv 2).symm.toContinuousLinearMap :=
  exists_hillMeanZeroComplexMap_localInverse

end NLS.Articles.KdVPseudomeasures
