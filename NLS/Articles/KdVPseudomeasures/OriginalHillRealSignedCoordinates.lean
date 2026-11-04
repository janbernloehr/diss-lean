import NLS.Articles.KdVPseudomeasures.OriginalHillSignedComplexCoordinates
import NLS.KdV.HillNativeRealLocalInverse

/-! The actual original real mean-zero potential is retained as the SAME
physical distribution in its closed real Fourier Banach model. The actual
signed coordinate map is real analytic and locally analytically invertible
at0, with the exact Fourier derivative and bounded Fourier inverse. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.Fourier NLS.Fourier.SmoothPeriodicTest
namespace NLS.Articles.KdVPseudomeasures

def originalHillRealSource (q : OriginalHminusOnePotential) : HillRealMeanZeroSource :=
  ⟨⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_mean_zero q⟩,originalPeriodOneCoefficients_real q⟩

theorem originalHillRealSource_same_distribution (q : OriginalHminusOnePotential) :
    periodOneOriginal (originalHillRealSource q).val.val=q.val :=
  periodOneOriginal_originalPeriodOneCoefficients q

def originalHillRealSignedCoordinates (q : OriginalHminusOnePotential) : HillRealSignedTarget :=
  hillRealSignedMap (originalHillRealSource q)

theorem original_Hill_real_signed_matches_complex (q : OriginalHminusOnePotential) :
    (originalHillRealSignedCoordinates q : HillSignedComplexTarget)=originalHillSignedComplexCoordinates q := by
  rw [originalHillRealSignedCoordinates,hillRealSignedMap_coe]
  rfl

theorem original_Hill_real_signed_analytic : AnalyticOnNhd ℝ hillRealSignedMap univ :=
  analyticOnNhd_hillRealSignedMap

theorem original_Hill_real_signed_action (q : OriginalHminusOnePotential) (n : ℕ+) :
    (originalHillRealSignedCoordinates q).val.val.val ((n:ℕ):ℤ)*
      (originalHillRealSignedCoordinates q).val.val.val (-((n:ℕ):ℤ))=
        hillHminusCanonicalAction n (originalPeriodOneCoefficients q) := by
  rw [original_Hill_real_signed_matches_complex]
  exact original_Hill_signed_complex_action q n

theorem original_Hill_real_signed_derivative_equiv :
    fderiv ℝ hillRealSignedMap 0=(WeightedCoeff.realMeanZeroHalfFourierEquiv 2).toContinuousLinearMap :=
  fderiv_hillRealSignedMap_zero

theorem original_Hill_real_signed_derivative_even_modes (q : OriginalHminusOnePotential) (n : ℕ+) :
    ((fderiv ℝ hillRealSignedMap 0) (originalHillRealSource q)).val.val.val ((n:ℕ):ℤ)=
      q.val.val (mode (-(2*(n:ℤ))))/(Real.sqrt (2*Real.pi*(n:ℕ)):ℂ) ∧
    ((fderiv ℝ hillRealSignedMap 0) (originalHillRealSource q)).val.val.val (-((n:ℕ):ℤ))=
      q.val.val (mode (2*(n:ℤ)))/(Real.sqrt (2*Real.pi*(n:ℕ)):ℂ) := by
  rw [fderiv_hillRealSignedMap_zero_apply,fderiv_hillRealSignedMap_zero_apply,
    WeightedCoeff.halfFourierSymbol_neg,WeightedCoeff.halfFourierSymbol_positive]
  simp only [originalHillRealSource,originalPeriodOneCoefficients,periodOneOriginalExtract_apply,mul_neg,neg_neg]
  constructor <;> ring

theorem original_Hill_real_signed_localInverse :
    ∃ g : HillRealSignedTarget → HillRealMeanZeroSource, AnalyticAt ℝ g 0 ∧ g 0=0 ∧
      (∀ᶠ q in 𝓝 (0 : HillRealMeanZeroSource), g (hillRealSignedMap q)=q) ∧
      (∀ᶠ z in 𝓝 (0 : HillRealSignedTarget), hillRealSignedMap (g z)=z) ∧
      fderiv ℝ g 0=(WeightedCoeff.realMeanZeroHalfFourierEquiv 2).symm.toContinuousLinearMap :=
  exists_hillRealSignedMap_localInverse

end NLS.Articles.KdVPseudomeasures
