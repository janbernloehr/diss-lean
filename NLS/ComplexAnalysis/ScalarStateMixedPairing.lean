import NLS.ComplexAnalysis.ScalarStateSquaredPairing

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra
open scoped ENNReal

namespace NLS.ComplexAnalysis

def scalarStateMixedPairing (A C B : Curve (ℂ × ℂ)) : ℂ :=
  NLS.FunctionalAnalysis.unitComplexCurveIntegral
    ((((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp A)^2)*
      (((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp C)*((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp B)+
        ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp C)*((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp B)))

theorem scalarStateMixedPairing_eq_integral (A C B : Curve (ℂ × ℂ)) :
    scalarStateMixedPairing A C B=∫ x in (0 : ℝ)..1,
      (NLS.LinearVolterra.extend A x).1^2*
        ((NLS.LinearVolterra.extend C x).2*(NLS.LinearVolterra.extend B x).1+
          (NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend B x).2) := rfl

theorem continuous_scalarStateMixedPairing :
    Continuous (fun p : Curve (ℂ × ℂ) × (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) =>
      scalarStateMixedPairing p.1 p.2.1 p.2.2) := by
  have hf : Continuous (fun A : Curve (ℂ × ℂ) => (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp A) :=
    (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp
  have hg : Continuous (fun A : Curve (ℂ × ℂ) => (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp A) :=
    (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).continuous_postcomp
  exact NLS.FunctionalAnalysis.unitComplexCurveIntegral.continuous.comp
    (((hf.comp continuous_fst).pow 2).mul
      (((hg.comp continuous_snd.fst).mul (hf.comp continuous_snd.snd)).add
        ((hf.comp continuous_snd.fst).mul (hg.comp continuous_snd.snd))))

end NLS.ComplexAnalysis
