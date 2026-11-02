import NLS.FunctionalAnalysis.LinearVolterraFlow
import NLS.ZakharovShabat.ClassicalMonodromyAnalytic

/-! # The physical ZS discriminant as a basis-free Volterra trace -/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

theorem solutionMap_classicalCoefficientCurve (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0 : ℝ) 1) (v : ℂ × ℂ) :
    solutionMap (classicalCoefficientCurveCLM (z,φ)) t v = classicalSolution φ z v t := by
  simp only [solutionMap_apply, realCoefficient_classicalCoefficientCurve, classicalSolution]

/-- No matrix convention or field relabeling is hidden in the trace adapter. -/
theorem classicalDiscriminant_eq_flowTrace (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminant φ z = LinearMap.trace ℂ (ℂ × ℂ)
      (solutionMap (classicalCoefficientCurveCLM (z,φ))
        ⟨1,by constructor <;> norm_num⟩).toLinearMap := by
  rw [trace_pairCLM]
  simp only [solutionMap_classicalCoefficientCurve, classicalDiscriminant,
    classicalMonodromy, classicalFundamentalMatrix, Matrix.trace_fin_two]
  rfl

end NLS.ZakharovShabat
