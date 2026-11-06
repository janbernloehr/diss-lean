import NLS.KdV.ClassicalHillWeightedTraceRemainder
import NLS.KdV.HillContinuousPotentialMass
import NLS.KdV.HillHminusOriginalSource
import NLS.Fourier.IntervalBilinearParseval

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.Fourier NLS.ComplexAnalysis
namespace NLS.KdV

/-- The sharp first-mean-subtracted trace estimate on the ACTUAL complex
unit-period L2 source. The original Fourier mean is retained literally. -/
theorem hillL2Discriminant_first_order_remainder_bound
    (p : Coeff 2) (z : ℂ) (hz : z ≠ 0) (hsmall : 4*‖p‖ ≤ ‖z‖) :
    ‖hillL2Discriminant (Coeff.periodDouble p) (z^2) - 2*cos z - sin z/z * p 0‖ ≤
      16 * Real.exp |z.im| * ‖p‖^2 / ‖z‖^2 := by
  have hfinite (a : ℤ →₀ ℂ) (ha : ‖Coeff.ofFinsupp (p := 2) a‖ ≤ ‖p‖) :
      ‖hillL2Discriminant (Coeff.periodDouble (Coeff.ofFinsupp (p := 2) a)) (z^2) -
        2*cos z - sin z/z * a 0‖ ≤ 16 * Real.exp |z.im| * ‖p‖^2 / ‖z‖^2 := by
    let A := Coeff.ofFinsupp (p := 1) a
    let Q := continuousSynthesis (Coeff.periodDouble A)
    have hQ : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) =
        Coeff.periodDouble (Coeff.ofFinsupp (p := 2) a) := by
      ext k
      rw [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,fourierCoeff_continuousSynthesis]
      by_cases hk : k%2=0
      · have he : k=2*(k/2) := by omega
        rw [he]
        simp only [Coeff.periodDouble_even]
        rfl
      · have he : k=2*(k/2)+1 := by omega
        rw [he]
        simp only [Coeff.periodDouble_odd]
    have hmean : (∫ s in (0:ℝ)..1, NLS.LinearVolterra.extend (hillUnitPotentialCurve Q) s) = a 0 := by
      have hs := periodOneCoefficient_synthesis A 0
      rw [periodOneCoefficient,←unitFourierCoefficient_eq_fourierCoeffOn,unitFourierCoefficient] at hs
      simp only [mul_zero,neg_zero,wave_zero,mul_one,Coeff.ofFinsupp_apply,A] at hs
      rw [←hs]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hs
      dsimp only [NLS.LinearVolterra.extend,hillUnitPotentialCurve,ContinuousMap.coe_mk]
      rw [projIcc_of_mem _ hs]
      rfl
    have hM : classicalHillPotentialMass (hillUnitPotentialCurve Q) ≤ 2*‖p‖ := by
      have hh := classicalHillPotentialMass_continuous_bound Q
      rw [hQ,Coeff.norm_periodDouble] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left ha (by norm_num))
    have hm : classicalHillPotentialMass (hillUnitPotentialCurve Q) / ‖z‖ ≤ 1/2 := by
      apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
      linarith
    have hb := classicalHillDiscriminant_first_order_remainder_bound (hillUnitPotentialCurve Q) z hz hm
    rw [hmean,←hillL2Discriminant_eq_classical,hQ] at hb
    apply hb.trans
    have hsq : (classicalHillPotentialMass (hillUnitPotentialCurve Q))^2 ≤ 4*‖p‖^2 := by
      nlinarith [classicalHillPotentialMass_nonneg (hillUnitPotentialCurve Q),norm_nonneg p]
    apply div_le_div_of_nonneg_right _ (sq_nonneg ‖z‖)
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4 * Real.exp |z.im|)]
  have hD : Continuous (fun a : Coeff 2 => hillL2Discriminant a (z^2)) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact ((analyticOnNhd_hillL2Discriminant_joint (z^2,a) (mem_univ _)).comp
      (f := fun b : Coeff 2 => (z^2,b)) (analyticAt_const.prod analyticAt_id)).continuousAt
  have hPD : Continuous (fun a : Coeff 2 => Coeff.periodDouble a) := Coeff.periodDouble.continuous
  have hF : Continuous (fun a : Coeff 2 =>
      ‖hillL2Discriminant (Coeff.periodDouble a) (z^2) - 2*cos z - sin z/z * a 0‖) := by
    exact (((hD.comp hPD).sub continuous_const).sub
      (continuous_const.mul (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous)).norm
  apply le_of_tendsto ((hF.tendsto p).comp (Coeff.tendsto_truncate (by simp) p))
  apply Filter.Eventually.of_forall
  intro s
  have he : Coeff.ofFinsupp (p := 2) (Coeff.finiteRestriction s p) = Coeff.truncate s p :=
    Coeff.ofFinsupp_finiteRestriction s p
  have hh := hfinite (Coeff.finiteRestriction s p) (by rw [he]; exact Coeff.norm_truncate_le (by norm_num) s p)
  have he0 : (Coeff.finiteRestriction s p) 0 = (Coeff.truncate s p) 0 := by
    exact congrArg (fun a : Coeff 2 => a 0) he
  change ‖hillL2Discriminant (Coeff.periodDouble (Coeff.truncate s p)) (z^2) -
    2*cos z - sin z/z * (Coeff.truncate s p) 0‖ ≤ _
  simpa only [he,he0] using hh

end NLS.KdV
