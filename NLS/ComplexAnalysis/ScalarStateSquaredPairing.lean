import NLS.ComplexAnalysis.ScalarStateCrossMass

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra
open scoped ComplexConjugate ENNReal

namespace NLS.ComplexAnalysis

def scalarStateSquaredPairing (A B : Curve (ℂ × ℂ)) : ℂ :=
  NLS.FunctionalAnalysis.unitComplexCurveIntegral
    ((((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp A)^2*
      ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp B))*((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp B))

theorem scalarStateSquaredPairing_eq_integral (A B : Curve (ℂ × ℂ)) :
    scalarStateSquaredPairing A B=∫ x in (0 : ℝ)..1,
      (NLS.LinearVolterra.extend A x).1^2*(NLS.LinearVolterra.extend B x).1*(NLS.LinearVolterra.extend B x).2 := rfl

theorem continuous_scalarStateSquaredPairing :
    Continuous (fun p : Curve (ℂ × ℂ) × Curve (ℂ × ℂ) => scalarStateSquaredPairing p.1 p.2) := by
  exact NLS.FunctionalAnalysis.unitComplexCurveIntegral.continuous.comp
    (((((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp continuous_fst).pow 2).mul
      ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp continuous_snd)).mul
      ((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp continuous_snd))

end NLS.ComplexAnalysis
