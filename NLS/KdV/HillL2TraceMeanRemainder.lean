import NLS.KdV.ClassicalHillTraceBorn
import NLS.KdV.HillContinuousPotentialMass
import NLS.KdV.HillL2EnergyDiscriminant
import NLS.ComplexAnalysis.CosineFourierIntegral

/-! # Quadratic complex L2 trace comparison at equal means -/
noncomputable section
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.ZakharovShabat NLS.Fourier
namespace NLS.KdV

private theorem finite_periodDouble_coefficients (a : ℤ →₀ ℂ) :
    SpectralWeight.one.toCoeff (hillContinuousCoefficients
      (continuousSynthesis (Coeff.periodDouble (Coeff.ofFinsupp (p := 1) a)))) =
        Coeff.periodDouble (Coeff.ofFinsupp (p := 2) a) := by
  ext j
  rw [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,fourierCoeff_continuousSynthesis]
  by_cases hj : j % 2 = 0
  · have he : j = 2*(j/2) := by omega
    rw [he,Coeff.periodDouble_even,Coeff.periodDouble_even]
    rfl
  · have he : j = 2*(j/2)+1 := by omega
    rw [he,Coeff.periodDouble_odd,Coeff.periodDouble_odd]

private theorem finite_periodDouble_mean_integral (a : ℤ →₀ ℂ) :
    (∫ s in (0 : ℝ)..1, NLS.LinearVolterra.extend (hillUnitPotentialCurve (continuousSynthesis
      (Coeff.periodDouble (Coeff.ofFinsupp (p := 1) a)))) s) = a 0 := by
  calc
    _ = ∫ s in (0 : ℝ)..1, periodOneSynthesis (Coeff.ofFinsupp (p := 1) a) s := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hsi : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
      simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hsi,hillUnitPotentialCurve,
        ContinuousMap.coe_mk,periodOneSynthesis]
    _ = _ := by rw [integral_eq_periodOneCoefficient_zero,periodOneCoefficient_synthesis]; rfl

private theorem finite_periodDouble_trace (a : ℤ →₀ ℂ) (z : ℂ) :
    hillL2Discriminant (Coeff.periodDouble (Coeff.ofFinsupp (p := 2) a)) (z^2) =
      classicalHillDiscriminant (hillUnitPotentialCurve (continuousSynthesis
        (Coeff.periodDouble (Coeff.ofFinsupp (p := 1) a)))) (z^2) := by
  rw [← finite_periodDouble_coefficients a,hillL2Discriminant_eq_classical]

private theorem hillL2Discriminant_mean_remainder_finite (u : Coeff 2) (z : ℂ) (hz : z ≠ 0)
    (H : ℝ) (hH : |z.im| ≤ H) (hsmall : 4*Real.exp H*‖u‖ ≤ ‖z‖)
    (a : ℤ →₀ ℂ) (ha : ‖Coeff.ofFinsupp (p := 2) a‖ ≤ ‖u‖) :
    ‖hillL2Discriminant (Coeff.periodDouble (Coeff.ofFinsupp (p := 2) a)) (z^2)-2*cos z-(sin z/z)*a 0‖ ≤
      16*(Real.exp H)^3*‖u‖^2/‖z‖^2 := by
  let Q := continuousSynthesis (Coeff.periodDouble (Coeff.ofFinsupp (p := 1) a))
  let q := hillUnitPotentialCurve Q
  have hcoef : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) =
      Coeff.periodDouble (Coeff.ofFinsupp (p := 2) a) := finite_periodDouble_coefficients a
  have hmass : classicalHillPotentialMass q ≤ 2*‖u‖ := by
    apply (classicalHillPotentialMass_continuous_bound Q).trans
    rw [hcoef,Coeff.norm_periodDouble]
    exact mul_le_mul_of_nonneg_left ha (by norm_num)
  have hs : Real.exp H/‖z‖*classicalHillPotentialMass q ≤ 1/2 := by
    apply (mul_le_mul_of_nonneg_left hmass (by positivity)).trans
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
    nlinarith [hsmall]
  have h := classicalHillDiscriminant_mean_remainder_bound q z hz H hH hs
  rw [finite_periodDouble_mean_integral,← finite_periodDouble_trace a z] at h
  apply h.trans
  calc
    _ ≤ 4*(Real.exp H)^3*(2*‖u‖)^2/‖z‖^2 := by gcongr; exact classicalHillPotentialMass_nonneg q
    _ = _ := by ring

theorem hillL2Discriminant_mean_remainder_bound (u : Coeff 2) (z : ℂ) (hz : z ≠ 0)
    (H : ℝ) (hH : |z.im| ≤ H) (hsmall : 4*Real.exp H*‖u‖ ≤ ‖z‖) :
    ‖hillL2Discriminant (Coeff.periodDouble u) (z^2)-2*cos z-(sin z/z)*u 0‖ ≤
      16*(Real.exp H)^3*‖u‖^2/‖z‖^2 := by
  have hs : Continuous (fun b : Coeff 2 => hillL2Discriminant (Coeff.periodDouble b) (z^2)) := by
    have hc := analyticOnNhd_hillL2Discriminant_joint.continuous
    have hm : Continuous (fun b : Coeff 2 => (z^2,Coeff.periodDouble b)) :=
      continuous_const.prodMk Coeff.periodDouble.continuous
    apply (hc.comp hm).congr
    intro b
    rfl
  have hc : Continuous (fun b : Coeff 2 => hillL2Discriminant (Coeff.periodDouble b) (z^2)-2*cos z-(sin z/z)*b 0) :=
    (hs.sub continuous_const).sub (continuous_const.mul ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous))
  apply le_of_tendsto (((hc.tendsto u).comp (Coeff.tendsto_truncate (by simp) u)).norm)
  apply Filter.Eventually.of_forall
  intro s
  have he := Coeff.ofFinsupp_finiteRestriction (p := 2) s u
  dsimp only [Function.comp_def]
  rw [← he]
  exact hillL2Discriminant_mean_remainder_finite u z hz H hH hsmall _
    (by rw [he]; exact Coeff.norm_truncate_le (by norm_num) s u)

theorem hillL2Discriminant_same_mean_comparison (u v : Coeff 2) (hmean : u 0 = v 0) (hv : ‖v‖ ≤ ‖u‖)
    (z : ℂ) (hz : z ≠ 0) (H : ℝ) (hH : |z.im| ≤ H) (hsmall : 4*Real.exp H*‖u‖ ≤ ‖z‖) :
    ‖hillL2Discriminant (Coeff.periodDouble u) (z^2)-hillL2Discriminant (Coeff.periodDouble v) (z^2)‖ ≤
      32*(Real.exp H)^3*‖u‖^2/‖z‖^2 := by
  have hu' := hillL2Discriminant_mean_remainder_bound u z hz H hH hsmall
  have hv' := hillL2Discriminant_mean_remainder_bound v z hz H hH
    ((mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 4*Real.exp H)).trans hsmall)
  have he : hillL2Discriminant (Coeff.periodDouble u) (z^2)-hillL2Discriminant (Coeff.periodDouble v) (z^2) =
      (hillL2Discriminant (Coeff.periodDouble u) (z^2)-2*cos z-(sin z/z)*u 0)-
        (hillL2Discriminant (Coeff.periodDouble v) (z^2)-2*cos z-(sin z/z)*v 0) := by rw [hmean]; ring
  rw [he]
  apply (norm_sub_le _ _).trans
  apply (add_le_add hu' hv').trans
  calc
    _ ≤ 16*(Real.exp H)^3*‖u‖^2/‖z‖^2+16*(Real.exp H)^3*‖u‖^2/‖z‖^2 := by gcongr
    _ = _ := by ring

end NLS.KdV
