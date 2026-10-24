import NLS.FunctionalAnalysis.NormalOperatorSpectralMeasure
import NLS.ZakharovShabat.L2WholeLineCayley
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary

/-! # Actual scalar spectral measures of the physical whole-line Cayley transform -/
noncomputable section
set_option autoImplicit false
open scoped CompactlySupported
open MeasureTheory NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The actual scalar CFC measure of the original physical Cayley transform.
This is a measure on its complex spectrum; transport to the real line and
absolute continuity require further theorems. -/
def wholeLineCayleySpectralMeasure (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2) :
    Measure (spectrum ℂ (wholeLineCayley u hu)) :=
  normalOperatorSpectralMeasure _ (wholeLineCayley_isStarNormal u hu) v

instance wholeLineCayleySpectralMeasure_isFiniteMeasure (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2) :
    IsFiniteMeasure (wholeLineCayleySpectralMeasure u hu v) := by
  unfold wholeLineCayleySpectralMeasure
  infer_instance

/-- The constructed physical measure has the original vector's squared norm as mass. -/
theorem wholeLineCayleySpectralMeasure_real_univ (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2) :
    (wholeLineCayleySpectralMeasure u hu v).real Set.univ = ‖v‖^2 :=
  normalOperatorSpectralMeasure_real_univ _ _ _

/-- Complex integration reproduces the actual physical Cayley functional calculus. -/
theorem integral_wholeLineCayleySpectralMeasure (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2)
    (f : C(spectrum ℂ (wholeLineCayley u hu), ℂ)) :
    ∫ x, f x ∂wholeLineCayleySpectralMeasure u hu v =
      inner ℂ v (cfcHom (wholeLineCayley_isStarNormal u hu) f v) :=
  integral_complex_normalOperatorSpectralMeasure _ _ _ _

/-- The CFC squared-norm identity holds for the actual whole-line Cayley measure. -/
theorem norm_wholeLineCayley_cfc_sq_eq_integral (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2)
    (f : C(spectrum ℂ (wholeLineCayley u hu), ℂ)) :
    ‖cfcHom (wholeLineCayley_isStarNormal u hu) f v‖^2 =
      ∫ x, ‖f x‖^2 ∂wholeLineCayleySpectralMeasure u hu v :=
  norm_cfcHom_apply_sq_eq_integral _ _ _ _

/-- The coordinate moment recovers the original bounded physical Cayley operator. -/
theorem integral_coordinate_wholeLineCayleySpectralMeasure (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2) :
    ∫ x, (x : ℂ) ∂wholeLineCayleySpectralMeasure u hu v =
      inner ℂ v (wholeLineCayley u hu v) :=
  integral_coordinate_normalOperatorSpectralMeasure _ _ _

/-- The actual Cayley spectrum lies on the unit circle. -/
theorem wholeLineCayley_spectrum_subset_unitary (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    spectrum ℂ (wholeLineCayley u hu) ⊆ unitary ℂ :=
  spectrum_subset_unitary_of_mem_unitary (wholeLineCayley_mem_unitary u hu)

end NLS.ZakharovShabat
