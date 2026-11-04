import NLS.KdV.HillContinuousPotentialMass
import NLS.KdV.HillL2EnergyDiscriminant
import NLS.SequenceSpaces.YoungInequality

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV



theorem hillL2Discriminant_free_error_small (q : Coeff 2) (z : ℂ) (hz : z ≠ 0)
    (H : ℝ) (hH : |z.im| ≤ H) (hsmall : 4*Real.exp H*‖q‖ ≤ ‖z‖) :
    ‖hillL2Discriminant q (z^2)-2*cos z‖ ≤ 8*(Real.exp H)^2*‖q‖/‖z‖ := by
  have hfinite (a : ℤ →₀ ℂ) (ha : ‖Coeff.ofFinsupp (p := 2) a‖ ≤ ‖q‖) :
      ‖hillL2Discriminant (Coeff.ofFinsupp (p := 2) a) (z^2)-2*cos z‖ ≤
        8*(Real.exp H)^2*‖q‖/‖z‖ := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) = Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    have hmass : classicalHillPotentialMass (hillUnitPotentialCurve Q) ≤ 2*‖q‖ := by
      apply (classicalHillPotentialMass_continuous_bound Q).trans
      rw [hq]
      exact mul_le_mul_of_nonneg_left ha (by norm_num)
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hs : Real.exp H/‖z‖*classicalHillPotentialMass (hillUnitPotentialCurve Q) ≤ 1/2 := by
      apply (mul_le_mul_of_nonneg_left hmass (by positivity)).trans
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hnorm).mpr
      nlinarith [hsmall]
    rw [← hq,hillL2Discriminant_eq_classical]
    apply (classicalHillDiscriminant_free_error_small (hillUnitPotentialCurve Q) z hz H hH hs).trans
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (by positivity)) (norm_nonneg z)).trans_eq
    ring
  have hlim : Tendsto (fun s : Finset ℤ =>
      ‖hillL2Discriminant (Coeff.truncate s q) (z^2)-2*cos z‖) atTop
      (𝓝 ‖hillL2Discriminant q (z^2)-2*cos z‖) := by
    have hc : Continuous (fun a : Coeff 2 => hillL2Discriminant a (z^2)) := by
      apply continuous_iff_continuousAt.mpr
      intro a
      exact ((analyticOnNhd_hillL2Discriminant_joint (z^2,a) (mem_univ _)).comp
        (f := fun b : Coeff 2 => (z^2,b)) (analyticAt_const.prod analyticAt_id)).continuousAt
    exact (((hc.tendsto q).comp (Coeff.tendsto_truncate (by simp) q)).sub tendsto_const_nhds).norm
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro s
  have ht : Coeff.ofFinsupp (p := 2) (Coeff.finiteRestriction s q) = Coeff.truncate s q :=
    Coeff.ofFinsupp_finiteRestriction s q
  rw [← ht]
  apply hfinite
  rw [ht]
  exact Coeff.norm_truncate_le (by norm_num) s q

end NLS.KdV
