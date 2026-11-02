import NLS.FunctionalAnalysis.ContinuousCurveIntegral

/-! # The bounded complex-linear integral of a continuous unit-interval curve -/
noncomputable section
open Set MeasureTheory
namespace NLS.LinearVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [SecondCountableTopology E]

/-- Integrate the actual continuous field over one unit of physical space. -/
def unitIntervalMean : Curve E →L[ℂ] E where
  toFun f := ∫ x in (0 : ℝ)..1, extend f x
  map_add' f g := by
    simp only [extend, ContinuousMap.add_apply]
    exact intervalIntegral.integral_add ((continuous_extend f).intervalIntegrable 0 1)
      ((continuous_extend g).intervalIntegrable 0 1)
  map_smul' c f := by
    simp only [extend, ContinuousMap.smul_apply, RingHom.id_apply]
    exact intervalIntegral.integral_smul c _
  cont := continuous_curve_intervalIntegral ⟨1,by constructor <;> norm_num⟩

@[simp] theorem unitIntervalMean_apply (f : Curve E) :
    unitIntervalMean f = ∫ x in (0 : ℝ)..1, extend f x := rfl

end NLS.LinearVolterra
