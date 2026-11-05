import NLS.KdV.ClassicalHillSheetRootFrequency
import NLS.KdV.HillDirichletSheetRoot
import NLS.KdV.HillContinuousPotentialMass
import NLS.ComplexAnalysis.SineFourierIntegral

/-! # Complex L2 Fourier approximation of the actual terminal sheet root

Finite Fourier approximation transports the actual Volterra estimate to
L2. The leading sequence consists of the original Fourier coefficients;
the remainder has inverse-frequency decay after multiplication by z.
-/
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

private theorem finite_periodDouble_sheet (a : ℤ →₀ ℂ) (z : ℂ) :
    hillDirichletSheetRoot (Coeff.periodDouble (Coeff.ofFinsupp (p := 2) a)) (z^2) =
      2*(classicalHillFlow (hillUnitPotentialCurve (continuousSynthesis
        (Coeff.periodDouble (Coeff.ofFinsupp (p := 1) a)))) (z^2) (0,1) 1).2-
          classicalHillDiscriminant (hillUnitPotentialCurve (continuousSynthesis
            (Coeff.periodDouble (Coeff.ofFinsupp (p := 1) a)))) (z^2) := by
  rw [hillDirichletSheetRoot,← finite_periodDouble_coefficients a,
    hillL2DirichletSlope_eq_classical,hillL2Discriminant_eq_classical]

private theorem finite_periodDouble_sine_integral (a : ℤ →₀ ℂ) (k : ℕ) :
    (∫ s in (0 : ℝ)..1, sin ((k : ℂ)*Real.pi*((2*s-1 : ℝ) : ℂ))*
      NLS.LinearVolterra.extend (hillUnitPotentialCurve (continuousSynthesis
        (Coeff.periodDouble (Coeff.ofFinsupp (p := 1) a)))) s) =
          (-1 : ℂ)^k*(a (-(k : ℤ))-a (k : ℤ))/(2*I) := by
  calc
    _ = ∫ s in (0 : ℝ)..1, sin ((k : ℂ)*Real.pi*((2*s-1 : ℝ) : ℂ))*
        periodOneSynthesis (Coeff.ofFinsupp (p := 1) a) s := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hsi : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
      simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hsi,hillUnitPotentialCurve,
        ContinuousMap.coe_mk,periodOneSynthesis]
    _ = _ := by
      rw [integral_sin_nat_frequency _ (continuous_periodOneSynthesis _),
        periodOneCoefficient_synthesis,periodOneCoefficient_synthesis]
      rfl

private theorem hillL2SheetRoot_fourier_remainder_finite
    (u : Coeff 2) (k : ℕ) (z : ℂ) (hz : z ≠ 0)
    (hδ : ‖z-(k : ℂ)*Real.pi‖ ≤ 1) (him : |z.im| ≤ 1)
    (hsmall : 4*Real.exp 1*‖u‖ ≤ ‖z‖) (a : ℤ →₀ ℂ) (ha : ‖Coeff.ofFinsupp (p := 2) a‖ ≤ ‖u‖) :
      ‖z*hillDirichletSheetRoot (Coeff.periodDouble (Coeff.ofFinsupp (p := 2) a)) (z^2)-
        (-1 : ℂ)^k*((Coeff.ofFinsupp (p := 2) a) (-(k : ℤ))-(Coeff.ofFinsupp (p := 2) a) (k : ℤ))/(2*I)‖ ≤
        16*(Real.exp 1)^3*‖u‖^2/‖z‖+2*Real.exp 1*‖z-(k : ℂ)*Real.pi‖*‖u‖ := by
  let a1 := Coeff.ofFinsupp (p := 1) a
  let Q := continuousSynthesis (Coeff.periodDouble a1)
  let q := hillUnitPotentialCurve Q
  have hcoef : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) =
      Coeff.periodDouble (Coeff.ofFinsupp (p := 2) a) := finite_periodDouble_coefficients a
  have hmass : classicalHillPotentialMass q ≤ 2*‖u‖ := by
    apply (classicalHillPotentialMass_continuous_bound Q).trans
    rw [hcoef,Coeff.norm_periodDouble]
    exact mul_le_mul_of_nonneg_left ha (by norm_num)
  have hs : Real.exp 1/‖z‖*classicalHillPotentialMass q ≤ 1/2 := by
    apply (mul_le_mul_of_nonneg_left hmass (by positivity)).trans
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
    nlinarith [hsmall]
  have hlead := finite_periodDouble_sine_integral a k
  have h := classicalHillSheetRoot_frequency_remainder_bound q z hz ((k : ℝ)*Real.pi) 1 him hs
  simp only [ofReal_mul,ofReal_natCast] at h hlead
  rw [hlead] at h
  have he := finite_periodDouble_sheet a z
  rw [← he] at h
  apply h.trans
  calc
    _ ≤ 4*(Real.exp 1)^3*(2*‖u‖)^2/‖z‖+
        Real.exp 1*‖z-(k : ℂ)*Real.pi‖*(2*‖u‖) := by
      gcongr <;> exact classicalHillPotentialMass_nonneg q
    _ = _ := by ring

theorem hillL2SheetRoot_fourier_remainder_bound (u : Coeff 2) (k : ℕ) (z : ℂ)
    (hz : z ≠ 0) (hδ : ‖z-(k : ℂ)*Real.pi‖ ≤ 1)
    (hsmall : 4*Real.exp 1*‖u‖ ≤ ‖z‖) :
    ‖z*hillDirichletSheetRoot (Coeff.periodDouble u) (z^2)-
      (-1 : ℂ)^k*(u (-(k : ℤ))-u (k : ℤ))/(2*I)‖ ≤
      16*(Real.exp 1)^3*‖u‖^2/‖z‖+2*Real.exp 1*‖z-(k : ℂ)*Real.pi‖*‖u‖ := by
  have him : |z.im| ≤ 1 := by
    have h := abs_im_le_norm (z-(k : ℂ)*Real.pi)
    simpa only [sub_im,mul_im,natCast_im,ofReal_im,mul_zero,zero_mul,add_zero,sub_zero] using h.trans hδ
  have hs : Continuous (fun b : Coeff 2 => hillDirichletSheetRoot (Coeff.periodDouble b) (z^2)) := by
    have hc := analyticOnNhd_hillDirichletSheetRoot_joint.continuous
    have hm : Continuous (fun b : Coeff 2 => (z^2,Coeff.periodDouble b)) :=
      continuous_const.prodMk Coeff.periodDouble.continuous
    apply (hc.comp hm).congr
    intro b
    rfl
  have hc : Continuous (fun b : Coeff 2 => z*hillDirichletSheetRoot (Coeff.periodDouble b) (z^2)-
      (-1 : ℂ)^k*(b (-(k : ℤ))-b (k : ℤ))/(2*I)) := by
    exact (continuous_const.mul hs).sub (continuous_const.mul
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-(k : ℤ))).continuous).sub ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).continuous)) |>.div_const _)
  apply le_of_tendsto (((hc.tendsto u).comp (Coeff.tendsto_truncate (by simp) u)).norm)
  apply Filter.Eventually.of_forall
  intro s
  have he := Coeff.ofFinsupp_finiteRestriction (p := 2) s u
  dsimp only [Function.comp_def]
  rw [← he]
  exact hillL2SheetRoot_fourier_remainder_finite u k z hz hδ him hsmall _
    (by rw [he]; exact Coeff.norm_truncate_le (by norm_num) s u)

end NLS.KdV
