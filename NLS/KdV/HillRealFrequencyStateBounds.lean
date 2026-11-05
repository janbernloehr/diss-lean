import NLS.KdV.HillRoughStateErrors
import NLS.ComplexAnalysis.SineApproximationMass

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- All four original fundamental-state components have their physical
frequency scaling on every sufficiently high positive real frequency. -/
theorem hillL2FrequencyStateCurve_real_scaled_bounds
    (q : Coeff 2) (r : ℝ) (hr : 0<r) (hsmall : 4*‖q‖≤r)
    (t : Icc (0 : ℝ) 1) :
    ‖(hillL2FrequencyStateCurve q r (0,1) t).1‖≤2/r ∧
    ‖(hillL2FrequencyStateCurve q r (0,1) t).2‖≤2 ∧
    ‖(hillL2FrequencyStateCurve q r (1,0) t).1‖≤2 ∧
    ‖(hillL2FrequencyStateCurve q r (1,0) t).2‖≤2*r := by
  have hrn : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  have hs : 4*Real.exp 0*‖q‖≤‖(r : ℂ)‖ := by
    simpa only [Real.exp_zero,mul_one,norm_real,Real.norm_of_nonneg hr.le] using hsmall
  have hS := hillL2FrequencyStateCurve_position_bound_small q r hrn 0 (by simp) hs (0,1) t
  have hC := hillL2FrequencyStateCurve_position_bound_small q r hrn 0 (by simp) hs (1,0) t
  have hSd := (hillL2FrequencyStateCurve_free_errors_small q r hrn 0 (by simp) hs (0,1) t).2
  have hCd := (hillL2FrequencyStateCurve_free_errors_small q r hrn 0 (by simp) hs (1,0) t).2
  simp only [norm_zero,norm_one,Real.exp_zero,one_pow,one_div,zero_add,add_zero,mul_one,mul_zero,
    zero_div,norm_real,Real.norm_of_nonneg hr.le] at hS hC hSd hCd
  have htrig := norm_trig_mul_real_le (r : ℂ) 0 t.val (by simp) t.property
  simp only [Real.exp_zero] at htrig
  have hSn := norm_le_norm_sub_add (hillL2FrequencyStateCurve q r (0,1) t).2 (cos ((r : ℂ)*t.val))
  have hCn := norm_le_norm_sub_add (hillL2FrequencyStateCurve q r (1,0) t).2 (-r*sin ((r : ℂ)*t.val))
  have hcos : ‖cos ((r : ℂ)*t.val)‖≤1 := htrig.1
  have hsin : ‖-(r : ℂ)*sin ((r : ℂ)*t.val)‖≤r := by
    rw [norm_mul,norm_neg,norm_real,Real.norm_of_nonneg hr.le]
    exact (mul_le_mul_of_nonneg_left htrig.2 hr.le).trans_eq (mul_one _)
  refine ⟨by simpa only [div_eq_mul_inv] using hS,?_,by simpa only [one_mul,mul_one] using hC,?_⟩
  · have he : 4*(r⁻¹)*‖q‖≤1 := by
      calc
        _ = (4*‖q‖)/r := by ring
        _ ≤ 1 := (div_le_one hr).mpr hsmall
    linarith
  · linarith

/-- A near-free real frequency and the actual scaled-sine error give an
inverse-square mass lower bound for the original rough Dirichlet state. -/
theorem hillL2FrequencyStateCurve_real_mass_lower
    (q : Coeff 2) (r : ℝ) (hr : 0<r) (n : ℕ) (hn : 1≤n)
    (hnear : |r-(n : ℝ)*Real.pi|≤1/8) (hsmall : 32*‖q‖≤r) :
    1/8≤r^2*scalarStateMass (hillL2FrequencyStateCurve q r (0,1)) := by
  have hs : 4*‖q‖≤r := by nlinarith [norm_nonneg q]
  have happrox (t : Icc (0 : ℝ) 1) :
      ‖(r : ℂ)*(hillL2FrequencyStateCurve q r (0,1) t).1-
        (Real.sin ((n : ℝ)*Real.pi*t.val) : ℂ)‖≤1/4 := by
    have herr := hillL2FrequencyStateCurve_scaled_sine_error q r hr hs t
    have hsin : ‖(Real.sin (r*t.val) : ℂ)-(Real.sin ((n : ℝ)*Real.pi*t.val) : ℂ)‖≤1/8 := by
      rw [←ofReal_sub,norm_real,Real.norm_eq_abs]
      apply (Real.abs_sin_sub_sin_le _ _).trans
      rw [←sub_mul,abs_mul,abs_of_nonneg t.property.1]
      exact (mul_le_of_le_one_right (abs_nonneg _) t.property.2).trans hnear
    have hb : 4*‖q‖/r≤1/8 := (div_le_iff₀ hr).mpr (by linarith)
    exact (norm_sub_le_norm_sub_add_norm_sub _ ((Real.sin (r*t.val) : ℝ) : ℂ) _).trans
      ((add_le_add (herr.trans hb) hsin).trans_eq (by norm_num))
  have hm := scalarStateMass_lower_of_sine_approx (hillL2FrequencyStateCurve q r (0,1)) r n hn happrox
  simpa only [norm_real,Real.norm_of_nonneg hr.le] using hm

end NLS.KdV
