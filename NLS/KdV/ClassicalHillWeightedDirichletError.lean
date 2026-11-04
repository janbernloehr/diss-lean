import NLS.KdV.ClassicalHillSmallPotential
import NLS.ComplexAnalysis.WeightedDuhamelIntegralBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



theorem classicalHillFlow_position_bound_weighted (q : Curve ℂ) (z : ℂ) (hz : z≠0)
    (hsmall : classicalHillPotentialMass q/‖z‖≤1/2)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖(classicalHillFlow q (z^2) v t).1‖≤
      2*Real.exp (|z.im| *t.val)*(‖v.1‖+‖v.2‖/‖z‖) := by
  let H := |z.im|
  let y : ℝ → ℂ := fun s => (classicalHillFlow q (z^2) v s).1
  let U : Curve ℂ := ⟨fun s => (Real.exp (-H*s.val) : ℂ)*y s,
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val))).mul
      ((continuous_classicalHillFlow q (z^2) v).fst.comp continuous_subtype_val)⟩
  let C := ‖U‖
  let B := ‖v.1‖+‖v.2‖/‖z‖
  let K := classicalHillPotentialMass q/‖z‖
  have hC0 : 0≤C := norm_nonneg U
  have hB0 : 0≤B := by dsimp only [B];positivity
  have hK0 : 0≤K := div_nonneg (classicalHillPotentialMass_nonneg q) (norm_nonneg z)
  have hnormU (r : Icc (0 : ℝ) 1) : ‖U r‖=Real.exp (-(H*r.val))*‖y r‖ := by
    change ‖(Real.exp (-H*r.val) : ℂ)*y r‖=_
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    rw [neg_mul]
  have hy (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) : ‖y s‖≤Real.exp (H*s)*C := by
    have hh := U.norm_coe_le_norm ⟨s,hs⟩
    rw [hnormU] at hh
    exact le_exp_mul_of_weight_le (H*s) _ C hh
  have hfree (r : Icc (0 : ℝ) 1) :
      ‖cos (z*r.val)*v.1+sin (z*r.val)/z*v.2‖≤Real.exp (H*r.val)*B := by
    have hc := norm_trig_mul_real_le_exp z r.val r.property.1
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,norm_div]
    apply (add_le_add (mul_le_mul_of_nonneg_right hc.1 (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc.2 (norm_nonneg z)) (norm_nonneg _))).trans_eq
    dsimp only [B,H]
    ring
  have herr (r : Icc (0 : ℝ) 1) :
      ‖y r-(cos (z*r.val)*v.1+sin (z*r.val)/z*v.2)‖≤Real.exp (H*r.val)*(K*C) := by
    dsimp only [y]
    rw [classicalHillFlow_sine_duhamel q z hz v r,add_sub_cancel_left]
    have hh := norm_sine_duhamel_integral_le_weighted (NLS.LinearVolterra.extend q) y z C r.val
      (continuous_extend q) r.property.1 (fun s hs => hy s ⟨hs.1,hs.2.trans r.property.2⟩)
    apply hh.trans
    apply (mul_le_mul_of_nonneg_left (classicalHillPotentialMass_partial_le q r) (by positivity)).trans_eq
    dsimp only [K,H]
    ring
  have hC : C≤B+K*C := by
    apply (ContinuousMap.norm_le U (by positivity)).mpr
    intro r
    rw [hnormU]
    have hh := (norm_le_norm_sub_add (y r) (cos (z*r.val)*v.1+sin (z*r.val)/z*v.2)).trans
      (add_le_add (herr r) (hfree r))
    have hw := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-(H*r.val))).le
    have hc (a : ℝ) : Real.exp (-(H*r.val))*(Real.exp (H*r.val)*a)=a := by
      simpa only [neg_neg] using exp_mul_cancel_weight (-(H*r.val)) a
    rw [mul_add,hc,hc] at hw
    linarith
  have hKC : K*C≤(1/2)*C := mul_le_mul_of_nonneg_right hsmall hC0
  have hub : C≤2*B := by nlinarith
  apply (hy t t.property).trans
  apply (mul_le_mul_of_nonneg_left hub (Real.exp_pos (H*t.val)).le).trans_eq
  dsimp only [B,H]
  ring

/-- The true exponential type is exp |Im z|, with a smallness threshold
depending only on the potential mass and |z|. -/
theorem classicalHillDirichlet_free_error_weighted (q : Curve ℂ) (z : ℂ) (hz : z≠0)
    (hsmall : classicalHillPotentialMass q/‖z‖≤1/2) :
    ‖(classicalHillFlow q (z^2) (0,1) 1).1-sin z/z‖≤
      2*Real.exp |z.im| *classicalHillPotentialMass q/‖z‖^2 := by
  have hS (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) :
      ‖(classicalHillFlow q (z^2) (0,1) s).1‖≤Real.exp (|z.im| *s)*(2/‖z‖) := by
    have hh := classicalHillFlow_position_bound_weighted q z hz hsmall (0,1) ⟨s,hs⟩
    simpa only [norm_zero,norm_one,zero_add,mul_one_div,mul_div_assoc,mul_comm (2 : ℝ)] using hh
  have he : (classicalHillFlow q (z^2) (0,1) 1).1-sin z/z=
      ∫ s in (0 : ℝ)..1,sin (z*((1-s : ℝ) : ℂ))/z*NLS.LinearVolterra.extend q s*
        (classicalHillFlow q (z^2) (0,1) s).1 := by
    have hh := classicalHillFlow_sine_duhamel q z hz (0,1) (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)
    simpa only [ofReal_one,mul_one,mul_zero,zero_add,add_sub_cancel_left] using
      congrArg (fun x : ℂ => x-sin z/z) hh
  rw [he]
  apply (norm_sine_duhamel_integral_le_weighted (NLS.LinearVolterra.extend q)
    (fun s => (classicalHillFlow q (z^2) (0,1) s).1) z (2/‖z‖) 1
    (continuous_extend q) (by norm_num) hS).trans_eq
  change (Real.exp (|z.im| *1)/‖z‖*(2/‖z‖))*classicalHillPotentialMass q=_
  rw [mul_one]
  ring

end NLS.KdV
