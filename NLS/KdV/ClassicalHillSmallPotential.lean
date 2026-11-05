import NLS.KdV.ClassicalHillDuhamel
import NLS.ComplexAnalysis.DuhamelIntegralBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV



def classicalHillPotentialMass (q : Curve ℂ) : ℝ :=
  ∫ s in (0 : ℝ)..1,‖NLS.LinearVolterra.extend q s‖

theorem classicalHillPotentialMass_nonneg (q : Curve ℂ) : 0 ≤ classicalHillPotentialMass q :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)

theorem classicalHillPotentialMass_partial_le (q : Curve ℂ) (t : Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..t.val,‖NLS.LinearVolterra.extend q s‖) ≤ classicalHillPotentialMass q := by
  exact intervalIntegral.integral_mono_interval le_rfl t.property.1 t.property.2
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    ((continuous_extend q).norm.intervalIntegrable 0 1)

theorem classicalHillFlow_position_bound_small (q : Curve ℂ) (z : ℂ) (hz : z ≠ 0)
    (H : ℝ) (hH : |z.im| ≤ H)
    (hsmall : Real.exp H/‖z‖*classicalHillPotentialMass q ≤ 1/2)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖(classicalHillFlow q (z^2) v t).1‖ ≤ 2*Real.exp H*(‖v.1‖+‖v.2‖/‖z‖) := by
  let y : ℝ → ℂ := fun s => (classicalHillFlow q (z^2) v s).1
  let U : Curve ℂ := ⟨fun s => y s,(continuous_classicalHillFlow q (z^2) v).fst.comp continuous_subtype_val⟩
  let C := ‖U‖
  let B := Real.exp H*(‖v.1‖+‖v.2‖/‖z‖)
  let K := Real.exp H/‖z‖*classicalHillPotentialMass q
  have hQ := classicalHillPotentialMass_nonneg q
  have hC0 : 0 ≤ C := norm_nonneg U
  have hB0 : 0 ≤ B := by dsimp only [B];positivity
  have hK0 : 0 ≤ K := by dsimp only [K];positivity
  have hfree (r : Icc (0 : ℝ) 1) :
      ‖cos (z*r.val)*v.1+sin (z*r.val)/z*v.2‖ ≤ B := by
    have hc := norm_trig_mul_real_le z H r.val hH r.property
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,norm_div]
    apply (add_le_add (mul_le_mul_of_nonneg_right hc.1 (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc.2 (norm_nonneg z)) (norm_nonneg _))).trans_eq
    dsimp only [B]
    ring
  have herr (r : Icc (0 : ℝ) 1) :
      ‖y r-(cos (z*r.val)*v.1+sin (z*r.val)/z*v.2)‖ ≤ K*C := by
    dsimp only [y]
    rw [classicalHillFlow_sine_duhamel q z hz v r,add_sub_cancel_left]
    have h := norm_sine_duhamel_integral_le (NLS.LinearVolterra.extend q) y z H C r.val
      (continuous_extend q) hH r.property (by
        intro s hs
        exact U.norm_coe_le_norm ⟨s,hs.1,hs.2.trans r.property.2⟩)
    apply h.trans
    apply (mul_le_mul_of_nonneg_left (classicalHillPotentialMass_partial_le q r) (by positivity)).trans_eq
    dsimp only [K]
    ring
  have hC : C ≤ B+K*C := by
    apply (ContinuousMap.norm_le U (by positivity)).mpr
    intro r
    have h := norm_le_norm_sub_add (y r) (cos (z*r.val)*v.1+sin (z*r.val)/z*v.2)
    exact h.trans ((add_le_add (herr r) (hfree r)).trans_eq (by ring))
  have hratio : K*C ≤ (1/2)*C := mul_le_mul_of_nonneg_right hsmall hC0
  have hub : C ≤ 2*B := by nlinarith
  exact (U.norm_coe_le_norm t).trans (hub.trans_eq (by dsimp only [B];ring))

theorem classicalHillDiscriminant_free_error_small (q : Curve ℂ) (z : ℂ) (hz : z ≠ 0)
    (H : ℝ) (hH : |z.im| ≤ H)
    (hsmall : Real.exp H/‖z‖*classicalHillPotentialMass q ≤ 1/2) :
    ‖classicalHillDiscriminant q (z^2)-2*cos z‖ ≤
      4*(Real.exp H)^2*classicalHillPotentialMass q/‖z‖ := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hC (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖(classicalHillFlow q (z^2) (1,0) s).1‖ ≤ 2*Real.exp H := by
    have h := classicalHillFlow_position_bound_small q z hz H hH hsmall (1,0) ⟨s,hs⟩
    simpa only [norm_one,norm_zero,zero_div,add_zero,mul_one] using h
  have hS (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖(classicalHillFlow q (z^2) (0,1) s).1‖ ≤ 2*Real.exp H/‖z‖ := by
    have h := classicalHillFlow_position_bound_small q z hz H hH hsmall (0,1) ⟨s,hs⟩
    simpa only [norm_one,norm_zero,zero_add,mul_one_div] using h
  have hc := norm_sine_duhamel_integral_le (NLS.LinearVolterra.extend q)
    (fun s => (classicalHillFlow q (z^2) (1,0) s).1) z H (2*Real.exp H) 1
    (continuous_extend q) hH ⟨by norm_num,le_rfl⟩ hC
  have hs := norm_cosine_duhamel_integral_le (NLS.LinearVolterra.extend q)
    (fun s => (classicalHillFlow q (z^2) (0,1) s).1) z H (2*Real.exp H/‖z‖) 1
    (continuous_extend q) hH ⟨by norm_num,le_rfl⟩ hS
  have hce : (classicalHillFlow q (z^2) (1,0) 1).1-cos z =
      ∫ s in (0 : ℝ)..1,sin (z*((1-s : ℝ) : ℂ))/z*NLS.LinearVolterra.extend q s*
        (classicalHillFlow q (z^2) (1,0) s).1 := by
    have h := classicalHillFlow_sine_duhamel q z hz (1,0) t
    simpa only [t,ofReal_one,mul_one,mul_zero,add_zero,add_sub_cancel_left] using
      congrArg (fun x : ℂ => x-cos z) h
  have hse : (classicalHillFlow q (z^2) (0,1) 1).2-cos z =
      ∫ s in (0 : ℝ)..1,cos (z*((1-s : ℝ) : ℂ))*NLS.LinearVolterra.extend q s*
        (classicalHillFlow q (z^2) (0,1) s).1 := by
    have h := classicalHillFlow_cosine_duhamel q z (0,1) t
    simpa only [t,ofReal_one,mul_one,mul_zero,zero_add,add_sub_cancel_left] using
      congrArg (fun x : ℂ => x-cos z) h
  have he : classicalHillDiscriminant q (z^2)-2*cos z =
      ((classicalHillFlow q (z^2) (1,0) 1).1-cos z)+
        ((classicalHillFlow q (z^2) (0,1) 1).2-cos z) := by
    rw [← classicalHillFlow_trace]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [hce,hse]
  apply (add_le_add hc hs).trans_eq
  change (Real.exp H/‖z‖*(2*Real.exp H))*classicalHillPotentialMass q+
    (Real.exp H*(2*Real.exp H/‖z‖))*classicalHillPotentialMass q = _
  ring

end NLS.KdV
