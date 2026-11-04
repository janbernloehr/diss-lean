import NLS.FunctionalAnalysis.LinearVolterra
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! # Bounded real linear integration on the unit interval for continuous curves. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate ENNReal
open NLS.LinearVolterra
namespace NLS.FunctionalAnalysis

def unitCurveIntegral : Curve ℝ →L[ℝ] ℝ :=
  ({ toFun := fun f => ∫ x in (0 : ℝ)..1, NLS.LinearVolterra.extend f x
     map_add' := by
       intro f g
       have hf : IntervalIntegrable (NLS.LinearVolterra.extend f) volume 0 1 := (continuous_extend f).intervalIntegrable 0 1
       have hg : IntervalIntegrable (NLS.LinearVolterra.extend g) volume 0 1 := (continuous_extend g).intervalIntegrable 0 1
       simpa only [NLS.LinearVolterra.extend,ContinuousMap.add_apply] using intervalIntegral.integral_add hf hg
     map_smul' := by
       intro c f
       simp only [NLS.LinearVolterra.extend,ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]
       exact intervalIntegral.integral_const_mul c _ } : Curve ℝ →ₗ[ℝ] ℝ).mkContinuous 1 (by
    intro f
    change ‖∫ x in (0 : ℝ)..1, NLS.LinearVolterra.extend f x‖≤1*‖f‖
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x (_ : x ∈ uIoc (0 : ℝ) 1) => ContinuousMap.norm_coe_le_norm f (projIcc 0 1 (by norm_num) x))
    simpa only [NLS.LinearVolterra.extend,sub_zero,abs_one,mul_one,one_mul] using hh)

@[simp] theorem unitCurveIntegral_apply (f : Curve ℝ) :
    unitCurveIntegral f = ∫ x in (0 : ℝ)..1, NLS.LinearVolterra.extend f x := rfl

end NLS.FunctionalAnalysis
