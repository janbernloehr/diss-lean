import NLS.FunctionalAnalysis.VectorSpectralFunctional

/-! # Actual scalar measures representing vector functionals -/
noncomputable section
set_option autoImplicit false
open scoped CompactlySupported
open MeasureTheory Complex
namespace NLS.FunctionalAnalysis
variable {X E : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The actual Riesz measure of the positive vector functional. -/
def vectorSpectralMeasure (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E)) (v : E) : Measure X :=
  RealRMK.rieszMeasure (vectorPositiveFunctional Φ v)

instance vectorSpectralMeasure_isFiniteMeasure
    (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E)) (v : E) :
    IsFiniteMeasure (vectorSpectralMeasure Φ v) := by
  unfold vectorSpectralMeasure
  infer_instance

/-- The constructed measure represents the original real vector functional. -/
theorem integral_vectorSpectralMeasure (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E))
    (v : E) (f : C_c(X, ℝ)) :
    ∫ x, f x ∂vectorSpectralMeasure Φ v =
      (inner ℂ v (Φ (complexifyCompactFunction f) v)).re :=
  RealRMK.integral_rieszMeasure (vectorPositiveFunctional Φ v) f

/-- The measure has the correct total mass for the original Hilbert vector. -/
theorem vectorSpectralMeasure_real_univ (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E))
    (v : E) : (vectorSpectralMeasure Φ v).real Set.univ = ‖v‖^2 := by
  let o : C_c(X, ℝ) := ⟨1, HasCompactSupport.of_compactSpace 1⟩
  have h := integral_vectorSpectralMeasure Φ v o
  have ho : complexifyCompactFunction o = 1 := by ext x; rfl
  rw [ho,map_one] at h
  change (∫ _x : X, (1 : ℝ) ∂vectorSpectralMeasure Φ v) = (inner ℂ v v).re at h
  have hn : (inner ℂ v v).re = ‖v‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [hn] at h
  simpa only [integral_const,smul_eq_mul,mul_one] using h

/-- The square of the operator-applied norm is exactly the scalar measure integral. -/
theorem norm_apply_sq_eq_integral_vectorSpectralMeasure
    (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E)) (v : E) (f : C(X, ℂ)) :
    ‖Φ f v‖^2 = ∫ x, ‖f x‖^2 ∂vectorSpectralMeasure Φ v := by
  let q : C_c(X, ℝ) := ⟨⟨fun x => ‖f x‖^2,f.continuous.norm.pow 2⟩,
    HasCompactSupport.of_compactSpace _⟩
  have h := integral_vectorSpectralMeasure Φ v q
  have hq : complexifyCompactFunction q = star f*f := by
    ext x
    change ((‖f x‖^2 : ℝ) : ℂ) = star (f x)*f x
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hq,map_mul,map_star] at h
  change (∫ x, ‖f x‖^2 ∂vectorSpectralMeasure Φ v) =
    (inner ℂ v (ContinuousLinearMap.adjoint (Φ f) (Φ f v))).re at h
  rw [ContinuousLinearMap.adjoint_inner_right] at h
  have hn : (inner ℂ (Φ f v) (Φ f v)).re = ‖Φ f v‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (Φ f v)
  rw [hn] at h
  exact h.symm

end NLS.FunctionalAnalysis
