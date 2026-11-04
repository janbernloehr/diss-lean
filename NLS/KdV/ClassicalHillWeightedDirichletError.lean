import NLS.KdV.ClassicalHillSmallPotential
import NLS.ComplexAnalysis.WeightedDuhamelIntegralBounds

/-! # Actual Hill Dirichlet error on the full complex frequency plane -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

/-- Weighting by exp(-H*t) makes the genuine scalar Volterra estimate
small at large frequency independently of the imaginary part. -/
theorem classicalHillFlow_position_weighted_bound (q : Curve ℂ) (z : ℂ) (hz : z≠0)
    (H : ℝ) (hH : |z.im|≤H) (hsmall : classicalHillPotentialMass q/‖z‖≤1/2)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖(classicalHillFlow q (z^2) v t).1‖≤
      2*Real.exp (H*t.val)*(‖v.1‖+‖v.2‖/‖z‖) := by
  let y : ℝ → ℂ := fun s => (classicalHillFlow q (z^2) v s).1
  have hy : Continuous y := (continuous_classicalHillFlow q (z^2) v).fst
  let U : Curve ℂ := ⟨fun s => (Real.exp (-H*s.val) : ℂ)*y s,by fun_prop⟩
  let C := ‖U‖
  let B := ‖v.1‖+‖v.2‖/‖z‖
  let K := classicalHillPotentialMass q/‖z‖
  have hQ := classicalHillPotentialMass_nonneg q
  have hC0 : 0≤C := norm_nonneg U
  have hB0 : 0≤B := by dsimp only [B];positivity
  have hK0 : 0≤K := by dsimp only [K];positivity
  have hcancel (r : ℝ) : Real.exp (-H*r)*Real.exp (H*r)=1 := by
    rw [← Real.exp_add,show -H*r+H*r=0 by ring,Real.exp_zero]
  have hUval (r : Icc (0 : ℝ) 1) : ‖U r‖=Real.exp (-H*r.val)*‖y r‖ := by
    change ‖(Real.exp (-H*r.val) : ℂ)*y r‖=_
    rw [norm_mul,norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hybound (r : Icc (0 : ℝ) 1) : ‖y r‖≤Real.exp (H*r.val)*C := by
    have hu := U.norm_coe_le_norm r
    rw [hUval] at hu
    calc
      _ = Real.exp (H*r.val)*(Real.exp (-H*r.val)*‖y r‖) := by
        rw [← mul_assoc,mul_comm (Real.exp (H*r.val)) (Real.exp (-H*r.val)),hcancel,one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hu (Real.exp_nonneg _)
  have hfree (r : Icc (0 : ℝ) 1) :
      ‖cos (z*r.val)*v.1+sin (z*r.val)/z*v.2‖≤Real.exp (H*r.val)*B := by
    have hc := norm_trig_mul_real_weighted_le z H r.val hH r.property.1
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,norm_div]
    apply (add_le_add (mul_le_mul_of_nonneg_right hc.1 (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc.2 (norm_nonneg z)) (norm_nonneg _))).trans_eq
    dsimp only [B]
    ring
  have herr (r : Icc (0 : ℝ) 1) :
      ‖y r-(cos (z*r.val)*v.1+sin (z*r.val)/z*v.2)‖≤Real.exp (H*r.val)*(K*C) := by
    dsimp only [y]
    rw [classicalHillFlow_sine_duhamel q z hz v r,add_sub_cancel_left]
    have hi := norm_sine_duhamel_integral_weighted_le (NLS.LinearVolterra.extend q) y z H C r.val
      (continuous_extend q) hH r.property.1 (by
        intro s hs
        exact hybound ⟨s,hs.1,hs.2.trans r.property.2⟩)
    apply hi.trans
    apply (mul_le_mul_of_nonneg_left (classicalHillPotentialMass_partial_le q r) (by positivity)).trans_eq
    dsimp only [K]
    ring
  have hC : C≤B+K*C := by
    apply (ContinuousMap.norm_le U (by positivity)).mpr
    intro r
    rw [hUval]
    have he : ‖y r‖≤Real.exp (H*r.val)*(B+K*C) := by
      exact (norm_le_norm_sub_add (y r) (cos (z*r.val)*v.1+sin (z*r.val)/z*v.2)).trans
        ((add_le_add (herr r) (hfree r)).trans_eq (by ring))
    calc
      _ ≤ Real.exp (-H*r.val)*(Real.exp (H*r.val)*(B+K*C)) :=
        mul_le_mul_of_nonneg_left he (Real.exp_nonneg _)
      _ = _ := by rw [← mul_assoc,hcancel,one_mul]
  have hratio : K*C≤(1/2)*C := mul_le_mul_of_nonneg_right hsmall hC0
  have hub : C≤2*B := by nlinarith
  exact (hybound t).trans ((mul_le_mul_of_nonneg_left hub (Real.exp_nonneg _)).trans_eq (by ring))

/-- The actual sine solution differs from its free value by order z^-2
with exactly one physical exponential factor, on all complex frequencies. -/
theorem classicalHillDirichlet_free_error_weighted (q : Curve ℂ) (z : ℂ) (hz : z≠0)
    (hsmall : classicalHillPotentialMass q/‖z‖≤1/2) :
    ‖(classicalHillFlow q (z^2) (0,1) 1).1-sin z/z‖≤
      2*Real.exp |z.im| *classicalHillPotentialMass q/‖z‖^2 := by
  have hS (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) :
      ‖(classicalHillFlow q (z^2) (0,1) s).1‖≤Real.exp (|z.im| *s)*(2/‖z‖) := by
    have h := classicalHillFlow_position_weighted_bound q z hz |z.im| le_rfl hsmall (0,1) ⟨s,hs⟩
    apply h.trans_eq
    simp only [norm_zero,norm_one,zero_add]
    ring
  have hi := norm_sine_duhamel_integral_weighted_le (NLS.LinearVolterra.extend q)
    (fun s => (classicalHillFlow q (z^2) (0,1) s).1) z |z.im| (2/‖z‖) 1
    (continuous_extend q) le_rfl (by norm_num) hS
  have he : (classicalHillFlow q (z^2) (0,1) 1).1-sin z/z=
      ∫ s in (0 : ℝ)..1,sin (z*((1-s : ℝ) : ℂ))/z*NLS.LinearVolterra.extend q s*
        (classicalHillFlow q (z^2) (0,1) s).1 := by
    have h := classicalHillFlow_sine_duhamel q z hz (0,1) ⟨1,by norm_num⟩
    simpa only [ofReal_one,mul_one,mul_zero,zero_add,add_sub_cancel_left] using
      congrArg (fun x : ℂ => x-sin z/z) h
  rw [he]
  apply hi.trans_eq
  simp only [mul_one]
  change (Real.exp |z.im|/‖z‖*(2/‖z‖))*classicalHillPotentialMass q=_
  ring

end NLS.KdV
