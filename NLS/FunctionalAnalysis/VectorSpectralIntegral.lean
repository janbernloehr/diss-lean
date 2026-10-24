import NLS.FunctionalAnalysis.VectorSpectralMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Complex integral representation for actual scalar spectral measures -/
noncomputable section
set_option autoImplicit false
open scoped CompactlySupported
open MeasureTheory Complex
namespace NLS.FunctionalAnalysis
variable {X E : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
/-- Real test functions have real expectation under the actual star homomorphism. -/
theorem inner_complexify_eq_ofReal (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E))
    (v : E) (f : C_c(X, ℝ)) :
    inner ℂ v (Φ (complexifyCompactFunction f) v) =
      ((inner ℂ v (Φ (complexifyCompactFunction f) v)).re : ℂ) := by
  have hs : IsSelfAdjoint (Φ (complexifyCompactFunction f)) := by
    change star (Φ (complexifyCompactFunction f)) = Φ (complexifyCompactFunction f)
    rw [← map_star]
    congr 1
    ext x
    simp [complexifyCompactFunction]
  exact (hs.isSymmetric.coe_re_inner_self_apply v).symm

/-- The actual Riesz measure represents the entire complex vector functional. -/
theorem integral_complex_vectorSpectralMeasure
    (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E)) (v : E) (f : C(X, ℂ)) :
    ∫ x, f x ∂vectorSpectralMeasure Φ v = inner ℂ v (Φ f v) := by
  let r : C_c(X, ℝ) := ⟨⟨fun x => (f x).re,continuous_re.comp f.continuous⟩,
    HasCompactSupport.of_compactSpace _⟩
  let j : C_c(X, ℝ) := ⟨⟨fun x => (f x).im,continuous_im.comp f.continuous⟩,
    HasCompactSupport.of_compactSpace _⟩
  have hsplit : f = complexifyCompactFunction r+I • complexifyCompactFunction j := by
    ext x
    change f x = (f x).re+I*(f x).im
    rw [mul_comm]
    exact (re_add_im (f x)).symm
  have hr := integral_vectorSpectralMeasure Φ v r
  have hj := integral_vectorSpectralMeasure Φ v j
  have hfi : Integrable f (vectorSpectralMeasure Φ v) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x, (f x).re ∂vectorSpectralMeasure Φ v) = _ at hr
  change (∫ x, (f x).im ∂vectorSpectralMeasure Φ v) = _ at hj
  have hre : (∫ x, (f x).re ∂vectorSpectralMeasure Φ v) =
      (∫ x, f x ∂vectorSpectralMeasure Φ v).re := integral_re hfi
  have him : (∫ x, (f x).im ∂vectorSpectralMeasure Φ v) =
      (∫ x, f x ∂vectorSpectralMeasure Φ v).im := integral_im hfi
  calc
    (∫ x, f x ∂vectorSpectralMeasure Φ v) =
        (∫ x, (f x).re ∂vectorSpectralMeasure Φ v)+
          I*(∫ x, (f x).im ∂vectorSpectralMeasure Φ v) := by
      rw [hre,him,mul_comm]
      exact (re_add_im _).symm
    _ = (inner ℂ v (Φ (complexifyCompactFunction r) v)).re+
          I*(inner ℂ v (Φ (complexifyCompactFunction j) v)).re := by rw [hr,hj]
    _ = inner ℂ v (Φ (complexifyCompactFunction r) v)+
          I*inner ℂ v (Φ (complexifyCompactFunction j) v) := by
      rw [← inner_complexify_eq_ofReal Φ v r,← inner_complexify_eq_ofReal Φ v j]
    _ = inner ℂ v (Φ f v) := by
      conv_rhs => rw [hsplit]
      simp only [map_add,map_smul,add_apply,smul_apply,
        inner_add_right,inner_smul_right]

end NLS.FunctionalAnalysis
