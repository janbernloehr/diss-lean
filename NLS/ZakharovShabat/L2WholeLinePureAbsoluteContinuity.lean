import NLS.FunctionalAnalysis.VectorSpectralMeasureParallelogram
import NLS.FunctionalAnalysis.QuadraticMeasureDenseAC
import NLS.ZakharovShabat.L2WholeLineCompactSpectralAC

/-! # Pure absolute continuity for the original whole-line physical operator -/
noncomputable section
set_option autoImplicit false
open MeasureTheory NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The actual transported scalar measures retain the quadratic vector sum bound. -/
theorem wholeLineRealSpectralMeasure_add_le (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v w : WholeLineL2) :
    wholeLineRealSpectralMeasure u hu (v+w) ≤
      (wholeLineRealSpectralMeasure u hu v + wholeLineRealSpectralMeasure u hu v) +
        (wholeLineRealSpectralMeasure u hu w + wholeLineRealSpectralMeasure u hu w) := by
  have hm : Measurable (fun x : spectrum ℂ (wholeLineCayley u hu) => inverseCayleyReal x) :=
    measurable_inverseCayleyReal.comp measurable_subtype_coe
  have h := Measure.map_mono
    (vectorSpectralMeasure_add_le (cfcHom (wholeLineCayley_isStarNormal u hu)) v w) hm
  simpa only [wholeLineRealSpectralMeasure, wholeLineCayleySpectralMeasure,
    normalOperatorSpectralMeasure, Measure.map_add _ _ hm] using h

/-- Every actual scalar spectral measure of the original self-adjoint physical
whole-line operator is absolutely continuous with respect to Lebesgue measure.
The proof uses the original dense test domain, the actual Green resolvent,
and countability of the repeated-root exceptional set. -/
theorem wholeLineRealSpectralMeasure_absolutelyContinuous (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2) :
    wholeLineRealSpectralMeasure u hu v ≪ (volume : Measure ℝ) :=
  absolutelyContinuous_quadraticMeasure_of_denseRange
    (wholeLineRealSpectralMeasure u hu) (wholeLineRealSpectralMeasure_real_univ u hu)
    (wholeLineRealSpectralMeasure_add_le u hu) wholeLineTestInclusion
    denseRange_wholeLineTestInclusion volume
    (wholeLineRealSpectralMeasure_test_absolutelyContinuous u hu) v

/-- Every Lebesgue-null set has zero actual physical scalar spectral mass,
for every Hilbert vector. This excludes both atoms and singular continuous mass. -/
theorem wholeLineRealSpectralMeasure_null_of_volume_null (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2)
    (s : Set ℝ) (hs : volume s = 0) : wholeLineRealSpectralMeasure u hu v s = 0 :=
  wholeLineRealSpectralMeasure_absolutelyContinuous u hu v hs

end NLS.ZakharovShabat
