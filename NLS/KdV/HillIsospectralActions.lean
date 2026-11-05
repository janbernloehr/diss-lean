import NLS.KdV.HillActionAmplitudeSources
import NLS.KdV.HillIndexedDiscriminantSources

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Every actual physical moment is stationary in any direction annihilating
all fixed-energy discriminants. -/
theorem hillRealSourceMoment_isospectral_fderiv
    (n : ℕ) (hn : 1≤n) (m : ℕ) (h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E)
      (SpectralWeight.one.toCoeff q)) h=0) :
    (fderiv ℂ (hillRealSourceMoment q hq hr n m) (SpectralWeight.one.toCoeff q)) h=0 := by
  rw [hillRealSourceMoment_gradient q hq hr n hn m,hillPhysicalMomentGradient,hillEnergyGradientContour,
    map_circleIntegral (hillPhysicalDirectionPairing h)
      (circleIntegrable_hillEnergyGradientContour_integrand _ _ _ _
        (add_nonneg (hillRealGapContour_geometry q hq hr n hn).1
          (hillRealGapContour_geometry q hq hr n hn).2.1.le)
        (continuousOn_hillPhysicalMomentGradientWeight q hq hr n hn m))]
  simp only [map_smul,←hillEnergyDiscriminantGradient_represents_potential,hiso,smul_zero,
    circleIntegral,intervalIntegral.integral_zero]

/-- The positive actual action amplitude is stationary in every isospectral direction. -/
theorem hillLocalActionAmplitude_isospectral_fderiv
    (n : ℕ) (hn : 1≤n) (hgap : hillRealGapHalfLength q hq hr n≠0)
    (h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E)
      (SpectralWeight.one.toCoeff q)) h=0) :
    (fderiv ℂ (hillLocalActionAmplitude q hq hr n) (SpectralWeight.one.toCoeff q)) h=0 := by
  have hA := analyticAt_hillLocalActionAmplitude q hq hr n hn hgap
  have hF : AnalyticAt ℂ (fun p : Coeff 2 => 2*hillRealSourceMoment q hq hr n 0 p)
      (SpectralWeight.one.toCoeff q) :=
    analyticAt_const.mul (analyticAt_hillRealSourceMoment q hq hr n hn 0)
  have hne : hillLocalActionAmplitude q hq hr n (SpectralWeight.one.toCoeff q)≠0 := by
    rw [(eventually_hillLocalActionAmplitude_eq_physical q hq hr n hn).self_of_nhds]
    apply ofReal_ne_zero.mpr
    apply (Real.sqrt_pos.mpr ?_).ne'
    apply mul_pos (by norm_num)
    apply (hillRealGapIntegral_pos_iff q hq hr n hn).mpr
    apply lt_of_le_of_ne (monotone_hillRealLabels q hq hr (by omega))
    intro he
    exact hgap (by simp only [hillRealGapHalfLength,he,sub_self,zero_div])
  apply squareRoot_source_fderiv_eq_zero _ _ _ _ hA hF
    (Filter.Eventually.of_forall (fun p => complex_sqrt_sq _)) hne
  rw [fderiv_const_mul (analyticAt_hillRealSourceMoment q hq hr n hn 0).differentiableAt]
  simp only [smul_apply,smul_eq_mul,hillRealSourceMoment_isospectral_fderiv q hq hr n hn 0 h hiso,mul_zero]

end NLS.KdV
