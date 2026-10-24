import NLS.FunctionalAnalysis.VectorSpectralIntegral
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-! # Scalar spectral measures of an actual bounded normal operator -/
noncomputable section
set_option autoImplicit false
open scoped CompactlySupported
open MeasureTheory
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The scalar spectral measure comes from the actual continuous functional
calculus on the independently defined spectrum of the bounded operator. -/
def normalOperatorSpectralMeasure (U : E →L[ℂ] E) (hU : IsStarNormal U) (v : E) :
    Measure (spectrum ℂ U) := vectorSpectralMeasure (cfcHom hU) v

instance normalOperatorSpectralMeasure_isFiniteMeasure (U : E →L[ℂ] E)
    (hU : IsStarNormal U) (v : E) : IsFiniteMeasure (normalOperatorSpectralMeasure U hU v) := by
  unfold normalOperatorSpectralMeasure
  infer_instance

/-- The actual CFC measure has total mass equal to the squared Hilbert norm. -/
theorem normalOperatorSpectralMeasure_real_univ (U : E →L[ℂ] E)
    (hU : IsStarNormal U) (v : E) :
    (normalOperatorSpectralMeasure U hU v).real Set.univ = ‖v‖^2 :=
  vectorSpectralMeasure_real_univ _ _

/-- The representation formula retains the original bounded operator's CFC. -/
theorem integral_normalOperatorSpectralMeasure (U : E →L[ℂ] E)
    (hU : IsStarNormal U) (v : E) (f : C_c(spectrum ℂ U, ℝ)) :
    ∫ x, f x ∂normalOperatorSpectralMeasure U hU v =
      (inner ℂ v (cfcHom hU (complexifyCompactFunction f) v)).re :=
  integral_vectorSpectralMeasure _ _ _

/-- CFC norm identity against the constructed scalar spectral measure. -/
theorem norm_cfcHom_apply_sq_eq_integral (U : E →L[ℂ] E)
    (hU : IsStarNormal U) (v : E) (f : C(spectrum ℂ U, ℂ)) :
    ‖cfcHom hU f v‖^2 = ∫ x, ‖f x‖^2 ∂normalOperatorSpectralMeasure U hU v :=
  norm_apply_sq_eq_integral_vectorSpectralMeasure _ _ _

/-- Full complex integral representation for the actual normal operator. -/
theorem integral_complex_normalOperatorSpectralMeasure (U : E →L[ℂ] E)
    (hU : IsStarNormal U) (v : E) (f : C(spectrum ℂ U, ℂ)) :
    ∫ x, f x ∂normalOperatorSpectralMeasure U hU v = inner ℂ v (cfcHom hU f v) :=
  integral_complex_vectorSpectralMeasure _ _ _

/-- The coordinate moment recovers the original operator itself. -/
theorem integral_coordinate_normalOperatorSpectralMeasure (U : E →L[ℂ] E)
    (hU : IsStarNormal U) (v : E) :
    ∫ x, (x : ℂ) ∂normalOperatorSpectralMeasure U hU v = inner ℂ v (U v) := by
  have h := integral_complex_normalOperatorSpectralMeasure U hU v
    (ContinuousMap.restrict (spectrum ℂ U) (ContinuousMap.id ℂ))
  rwa [cfcHom_id] at h

end NLS.FunctionalAnalysis
