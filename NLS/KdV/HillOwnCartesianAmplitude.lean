import NLS.KdV.HillActionGapPrefactor
import NLS.KdV.HillOwnGapFactor

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillOwnCartesianAmplitude (n : ℕ) (hn : 1 ≤ n) : ℂ :=
  hillActionGapPrefactor q hq hr n*hillOwnGapFactor q hq hr n hn

theorem hillOwnCartesianAmplitude_closed (n : ℕ) (hn : 1 ≤ n)
    (hc : hillRealGapHalfLength q hq hr n = 0) : hillOwnCartesianAmplitude q hq hr n hn = 0 := by
  rw [hillOwnCartesianAmplitude,hillOwnGapFactor_closed q hq hr n hn hc,mul_zero]

theorem hillOwnCartesianAmplitude_eq_action_phase (n : ℕ) (hn : 1 ≤ n) :
    hillOwnCartesianAmplitude q hq hr n hn = (Real.sqrt (2*hillRealGapIntegral q hq hr n 0) : ℂ)*hillDirichletCirclePhase q hq hr n hn := by
  by_cases hc : hillRealGapHalfLength q hq hr n = 0
  · rw [hillOwnCartesianAmplitude_closed q hq hr n hn hc,
      sqrt_twice_hillAction_eq_halfLength_mul_prefactor q hq hr n hn,hc,ofReal_zero,zero_mul,zero_mul]
  · rw [hillOwnCartesianAmplitude,hillOwnGapFactor_eq_halfLength_mul_phase q hq hr n hn hc,
      sqrt_twice_hillAction_eq_halfLength_mul_prefactor q hq hr n hn]
    ring

theorem hillSpectralCartesian_eq_ownAmplitude_mul_correction (n : ℕ) (hn : 1 ≤ n) :
    hillSpectralCartesian q hq hr n hn = hillOwnCartesianAmplitude q hq hr n hn *
      Complex.exp (I*hillSummedRegularAbelianCorrection q hq hr n hn) := by
  rw [hillOwnCartesianAmplitude_eq_action_phase]
  rfl

theorem norm_hillOwnCartesianAmplitude (n : ℕ) (hn : 1 ≤ n) :
    ‖hillOwnCartesianAmplitude q hq hr n hn‖ = Real.sqrt (2*hillRealGapIntegral q hq hr n 0) := by
  by_cases hc : hillRealGapHalfLength q hq hr n = 0
  · rw [hillOwnCartesianAmplitude_closed q hq hr n hn hc,norm_zero,
      show Real.sqrt (2*hillRealGapIntegral q hq hr n 0) = 0 by
        have h := sqrt_twice_hillAction_eq_halfLength_mul_prefactor q hq hr n hn
        rw [hc,ofReal_zero,zero_mul] at h
        exact ofReal_eq_zero.mp h]
  · rw [hillOwnCartesianAmplitude_eq_action_phase,norm_mul,hillDirichletCirclePhase_norm q hq hr n hn hc,
      mul_one,norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

theorem hillOwnCartesianAmplitude_action_identity (n : ℕ) (hn : 1 ≤ n) :
    (hillOwnCartesianAmplitude q hq hr n hn).re^2+(hillOwnCartesianAmplitude q hq hr n hn).im^2 =
      2*hillRealGapIntegral q hq hr n 0 := by
  have hI : 0 ≤ hillRealGapIntegral q hq hr n 0 := by
    simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr n hn 0
  have hs := congrArg (fun t : ℝ => t^2) (norm_hillOwnCartesianAmplitude q hq hr n hn)
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) hI),Complex.sq_norm,Complex.normSq_apply] at hs
  nlinarith

end NLS.KdV
