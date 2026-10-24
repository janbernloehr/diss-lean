import NLS.FunctionalAnalysis.VectorSpectralMeasure

/-! # Bounding a spectral atom by an actual operator-applied norm -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLS.FunctionalAnalysis
variable {X E : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A continuous test function equal to one at a point bounds its actual
scalar spectral mass by the squared norm of the corresponding operator image. -/
theorem vectorSpectralMeasure_atom_le_norm_apply_sq
    (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E)) (v : E) (a : X)
    (f : C(X, ℂ)) (hf : f a = 1) :
    (vectorSpectralMeasure Φ v).real {a} ≤ ‖Φ f v‖^2 := by
  rw [norm_apply_sq_eq_integral_vectorSpectralMeasure]
  have hi : Integrable (fun x => ‖f x‖^2) (vectorSpectralMeasure Φ v) :=
    (f.continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_mono_measure (Measure.restrict_le_self (s := {a}))
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f x‖)) hi
  rw [integral_singleton] at h
  simpa [hf] using h

end NLS.FunctionalAnalysis
