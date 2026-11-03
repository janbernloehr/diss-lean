import NLS.KdV.HillDirichletCirclePhase
import NLS.KdV.HillRegularSumContinuity
import NLS.KdV.HillRealActionContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

omit h0q h0r in
def hillSpectralCartesian (n : ℕ) (hn : 1 ≤ n) : ℂ :=
  (Real.sqrt (2*hillRealGapIntegral q hq hr n 0) : ℂ)*hillDirichletCirclePhase q hq hr n hn *
    Complex.exp (I*hillSummedRegularAbelianCorrection q hq hr n hn)

theorem hillSpectralCartesian_closed (n : ℕ) (hn : 1 ≤ n)
    (hc : hillRealGapHalfLength q hq hr n = 0) : hillSpectralCartesian q hq hr n hn = 0 := by
  have hclosed : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n) := by
    unfold hillRealGapHalfLength at hc
    linarith
  rw [hillSpectralCartesian,hillRealGapIntegral_closed q hq hr n 0 hclosed,mul_zero,Real.sqrt_zero,ofReal_zero,zero_mul,zero_mul]

include h0q h0r

theorem norm_hillSpectralCartesian (n : ℕ) (hn : 1 ≤ n) :
    ‖hillSpectralCartesian q hq hr n hn‖ = Real.sqrt (2*hillRealGapIntegral q hq hr n 0) := by
  by_cases hc : hillRealGapHalfLength q hq hr n = 0
  · rw [hillSpectralCartesian_closed q hq hr n hn hc,norm_zero]
    have hclosed : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n) := by
      unfold hillRealGapHalfLength at hc
      linarith
    rw [hillRealGapIntegral_closed q hq hr n 0 hclosed,mul_zero,Real.sqrt_zero]
  have hexp : ‖Complex.exp (I*hillSummedRegularAbelianCorrection q hq hr n hn)‖ = 1 := by
    rw [Complex.norm_exp,mul_re,I_re,I_im,zero_mul,one_mul,
      hillSummedRegularAbelianCorrection_im_eq_zero h0q h0r q hq hr n hn,sub_zero,Real.exp_zero]
  rw [hillSpectralCartesian,norm_mul,norm_mul,hillDirichletCirclePhase_norm q hq hr n hn hc,hexp,
    mul_one,mul_one,norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

theorem hillSpectralCartesian_action_identity (n : ℕ) (hn : 1 ≤ n) :
    (hillSpectralCartesian q hq hr n hn).re^2+(hillSpectralCartesian q hq hr n hn).im^2 =
      2*hillRealGapIntegral q hq hr n 0 := by
  have hI : 0 ≤ hillRealGapIntegral q hq hr n 0 := by
    simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr n hn 0
  have h := norm_hillSpectralCartesian h0q h0r q hq hr n hn
  have hs := congrArg (fun t : ℝ => t^2) h
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) hI),Complex.sq_norm,Complex.normSq_apply] at hs
  nlinarith

theorem continuous_hillSpectralCartesian (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun p : RealPeriodOneHillPotential => hillSpectralCartesian p.val p.property.1 p.property.2 n hn) := by
  have hAmp : Continuous (fun p : RealPeriodOneHillPotential => Real.sqrt (2*hillRealGapIntegral p.val p.property.1 p.property.2 n 0)) :=
    Real.continuous_sqrt.comp (continuous_const.mul (continuous_hillRealGapIntegral n hn 0))
  have hExp : Continuous (fun p : RealPeriodOneHillPotential => Complex.exp (I*hillSummedRegularAbelianCorrection p.val p.property.1 p.property.2 n hn)) :=
    Complex.continuous_exp.comp (continuous_const.mul (continuous_hillSummedRegularAbelianCorrection h0q h0r n hn))
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hc : hillRealGapHalfLength p.val p.property.1 p.property.2 n = 0
  · have hz := hillSpectralCartesian_closed p.val p.property.1 p.property.2 n hn hc
    change Tendsto (fun r : RealPeriodOneHillPotential => hillSpectralCartesian r.val r.property.1 r.property.2 n hn) (𝓝 p)
      (𝓝 (hillSpectralCartesian p.val p.property.1 p.property.2 n hn))
    rw [hz]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have he : (fun r : RealPeriodOneHillPotential => ‖hillSpectralCartesian r.val r.property.1 r.property.2 n hn‖) =
        (fun r : RealPeriodOneHillPotential => Real.sqrt (2*hillRealGapIntegral r.val r.property.1 r.property.2 n 0)) :=
      funext (fun r => norm_hillSpectralCartesian h0q h0r r.val r.property.1 r.property.2 n hn)
    have hzero : Real.sqrt (2*hillRealGapIntegral p.val p.property.1 p.property.2 n 0) = 0 := by
      rw [← norm_hillSpectralCartesian h0q h0r p.val p.property.1 p.property.2 n hn,hz,norm_zero]
    rw [he]
    simpa only [hzero] using hAmp.tendsto p
  · exact ((Complex.continuous_ofReal.comp hAmp).continuousAt.mul
      (continuousAt_hillDirichletCirclePhase_open p.val p.property.1 p.property.2 n hn hc)).mul hExp.continuousAt

end NLS.KdV
