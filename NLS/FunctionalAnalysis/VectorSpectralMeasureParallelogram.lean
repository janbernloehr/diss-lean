import NLS.FunctionalAnalysis.VectorSpectralMeasure

/-! # The parallelogram identity for actual scalar spectral measures -/
noncomputable section
set_option autoImplicit false
open scoped CompactlySupported
open MeasureTheory Complex
namespace NLS.FunctionalAnalysis
variable {X E : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

instance vectorSpectralMeasure_regular
    (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E)) (v : E) :
    (vectorSpectralMeasure Φ v).Regular := by
  unfold vectorSpectralMeasure
  infer_instance

/-- The quadratic vector dependence is an identity of the constructed measures. -/
theorem vectorSpectralMeasure_parallelogram
    (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E)) (v w : E) :
    vectorSpectralMeasure Φ (v+w) + vectorSpectralMeasure Φ (v-w) =
      (vectorSpectralMeasure Φ v + vectorSpectralMeasure Φ v) +
        (vectorSpectralMeasure Φ w + vectorSpectralMeasure Φ w) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  simp only [integral_add_measure f.integrable f.integrable, integral_vectorSpectralMeasure]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, Complex.add_re, Complex.sub_re]
  ring

/-- Spectral mass of a sum is bounded by twice each summand's spectral mass. -/
theorem vectorSpectralMeasure_add_le
    (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E)) (v w : E) :
    vectorSpectralMeasure Φ (v+w) ≤
      (vectorSpectralMeasure Φ v + vectorSpectralMeasure Φ v) +
        (vectorSpectralMeasure Φ w + vectorSpectralMeasure Φ w) := by
  rw [← vectorSpectralMeasure_parallelogram]
  exact Measure.le_add_right le_rfl

end NLS.FunctionalAnalysis
