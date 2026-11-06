import NLS.KdV.HillLogNormingGradient

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal

namespace NLS.KdV

def hillPhysicalDirectionPairing (h : Coeff 2) : Curve ℂ →L[ℂ] ℂ :=
  -((ContinuousMap.evalCLM ℂ (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp
    (l2ScalarVolterraCLM (hillPhysicalDirection h).ofLp.2))

theorem hillPhysicalDirectionPairing_apply (h : Coeff 2) (w : Curve ℂ) :
    hillPhysicalDirectionPairing h w=
      ∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*NLS.LinearVolterra.extend w x := by
  change -(∫ x in (0 : ℝ)..1,(hillPhysicalDirection h).ofLp.2 x*NLS.LinearVolterra.extend w x)=_
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x _
  ring

end NLS.KdV
