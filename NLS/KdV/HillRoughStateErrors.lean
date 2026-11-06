import NLS.KdV.ClassicalHillStateErrors
import NLS.KdV.HillRoughSmallPotentialPosition

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.Fourier NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual rough scalar state retains the normalized all-point Volterra
errors for both position and velocity, in the original coefficient topology. -/
theorem hillL2FrequencyStateCurve_free_errors_small
    (q : Coeff 2) (z : ℂ) (hz : z≠0) (H : ℝ) (hH : |z.im|≤H)
    (hsmall : 4*Real.exp H*‖q‖≤‖z‖) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖(hillL2FrequencyStateCurve q z v t).1-
      (cos (z*t.val)*v.1+sin (z*t.val)/z*v.2)‖≤
        (4*(Real.exp H)^2/‖z‖)*(‖v.1‖+‖v.2‖/‖z‖)*‖q‖ ∧
    ‖(hillL2FrequencyStateCurve q z v t).2-
      (-z*sin (z*t.val)*v.1+cos (z*t.val)*v.2)‖≤
        (4*(Real.exp H)^2)*(‖v.1‖+‖v.2‖/‖z‖)*‖q‖ := by
  have hfinite (a : ℤ →₀ ℂ) (ha : ‖Coeff.ofFinsupp (p := 2) a‖≤‖q‖) :
      ‖(hillL2FrequencyStateCurve (Coeff.ofFinsupp (p := 2) a) z v t).1-
        (cos (z*t.val)*v.1+sin (z*t.val)/z*v.2)‖≤
          (4*(Real.exp H)^2/‖z‖)*(‖v.1‖+‖v.2‖/‖z‖)*‖q‖ ∧
      ‖(hillL2FrequencyStateCurve (Coeff.ofFinsupp (p := 2) a) z v t).2-
        (-z*sin (z*t.val)*v.1+cos (z*t.val)*v.2)‖≤
          (4*(Real.exp H)^2)*(‖v.1‖+‖v.2‖/‖z‖)*‖q‖ := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    have hmass : classicalHillPotentialMass (hillUnitPotentialCurve Q)≤2*‖q‖ := by
      apply (classicalHillPotentialMass_continuous_bound Q).trans
      rw [hq]
      exact mul_le_mul_of_nonneg_left ha (by norm_num)
    have hs : Real.exp H/‖z‖*classicalHillPotentialMass (hillUnitPotentialCurve Q)≤1/2 := by
      apply (mul_le_mul_of_nonneg_left hmass (by positivity)).trans
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
      nlinarith [hsmall]
    rw [←hq,hillL2FrequencyStateCurve_eq_classical]
    constructor
    · apply (classicalHillFlow_position_free_error_small (hillUnitPotentialCurve Q) z hz H hH hs v t).trans
      exact (mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (by ring)
    · apply (classicalHillFlow_velocity_free_error_small (hillUnitPotentialCurve Q) z hz H hH hs v t).trans
      exact (mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (by ring)
  have hc := (continuous_eval_const t).comp (continuous_hillL2FrequencyStateCurve z v)
  have hfirst : Continuous (fun a : Coeff 2 => ‖(hillL2FrequencyStateCurve a z v t).1-
      (cos (z*t.val)*v.1+sin (z*t.val)/z*v.2)‖) := (hc.fst.sub continuous_const).norm
  have hsecond : Continuous (fun a : Coeff 2 => ‖(hillL2FrequencyStateCurve a z v t).2-
      (-z*sin (z*t.val)*v.1+cos (z*t.val)*v.2)‖) := (hc.snd.sub continuous_const).norm
  have htrunc (s : Finset ℤ) := hfinite (Coeff.finiteRestriction s q) (by
    rw [Coeff.ofFinsupp_finiteRestriction]
    exact Coeff.norm_truncate_le (by norm_num) s q)
  constructor
  · apply le_of_tendsto ((hfirst.tendsto q).comp (Coeff.tendsto_truncate (by simp) q))
    apply Eventually.of_forall
    intro s
    have hh := (htrunc s).1
    rw [Coeff.ofFinsupp_finiteRestriction] at hh
    convert! hh using 1
  · apply le_of_tendsto ((hsecond.tendsto q).comp (Coeff.tendsto_truncate (by simp) q))
    apply Eventually.of_forall
    intro s
    have hh := (htrunc s).2
    rw [Coeff.ofFinsupp_finiteRestriction] at hh
    convert! hh using 1

/-- At a real positive frequency the actual scaled sine solution is close
to its free sine, uniformly throughout the physical interval. -/
theorem hillL2FrequencyStateCurve_scaled_sine_error
    (q : Coeff 2) (r : ℝ) (hr : 0<r) (hsmall : 4*‖q‖≤r)
    (t : Icc (0 : ℝ) 1) :
    ‖(r : ℂ)*(hillL2FrequencyStateCurve q r (0,1) t).1-(Real.sin (r*t.val) : ℂ)‖≤4*‖q‖/r := by
  have hrn : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  have hh := (hillL2FrequencyStateCurve_free_errors_small q r hrn 0 (by simp)
    (by simpa only [Real.exp_zero,mul_one,norm_real,Real.norm_of_nonneg hr.le] using hsmall) (0,1) t).1
  simp only [norm_zero,norm_one,Real.exp_zero,one_pow,one_div,zero_add,mul_zero,zero_add,mul_one,
    norm_real,Real.norm_of_nonneg hr.le] at hh
  have he : (r : ℂ)*(hillL2FrequencyStateCurve q r (0,1) t).1-(Real.sin (r*t.val) : ℂ)=
      (r : ℂ)*((hillL2FrequencyStateCurve q r (0,1) t).1-sin ((r : ℂ)*t.val)/(r : ℂ)) := by
    rw [Complex.ofReal_sin,ofReal_mul]
    field_simp
  rw [he,norm_mul,norm_real,Real.norm_of_nonneg hr.le]
  apply (mul_le_mul_of_nonneg_left hh hr.le).trans_eq
  field_simp

end NLS.KdV
