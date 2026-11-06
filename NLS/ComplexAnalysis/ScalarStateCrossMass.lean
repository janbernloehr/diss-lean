import NLS.FunctionalAnalysis.UnitComplexCurveIntegral
import NLS.ComplexAnalysis.ScalarStateMass

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra
open scoped ComplexConjugate ENNReal

namespace NLS.ComplexAnalysis

def scalarStateCrossMass (A B : Curve (ℂ × ℂ)) : ℂ :=
  NLS.FunctionalAnalysis.unitComplexCurveIntegral
    (((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp A)*((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp B))

theorem scalarStateCrossMass_eq_integral (A B : Curve (ℂ × ℂ)) :
    scalarStateCrossMass A B=∫ x in (0 : ℝ)..1,
      (NLS.LinearVolterra.extend A x).1*(NLS.LinearVolterra.extend B x).1 := rfl

theorem continuous_scalarStateCrossMass : Continuous (fun p : Curve (ℂ × ℂ) × Curve (ℂ × ℂ) => scalarStateCrossMass p.1 p.2) := by
  exact NLS.FunctionalAnalysis.unitComplexCurveIntegral.continuous.comp
    (((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp continuous_fst).mul
      ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp continuous_snd))

theorem scalarStateCrossMass_self_real (Y : Curve (ℂ × ℂ)) (hY : ∀ t, (Y t).1.im=0) :
    scalarStateCrossMass Y Y=(scalarStateMass Y : ℂ) := by
  rw [scalarStateCrossMass_eq_integral,scalarStateMass_eq_integral,← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x _
  have hh := hY (projIcc 0 1 (by norm_num) x)
  apply Complex.ext <;> simp only [NLS.LinearVolterra.extend,mul_re,mul_im,ofReal_re,ofReal_im,hh,normSq_apply,
    mul_zero,zero_mul,add_zero,sub_zero]

end NLS.ComplexAnalysis
