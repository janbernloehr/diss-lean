import NLS.Fourier.ComplexMeasureContinuousIntegral
import NLS.Fourier.RealContinuousFunctionalDecomposition
/-! # Complex Riesz representation on a compact space

The positive real Riesz theorem and the proved real-functional decomposition
give signed representation. Real and imaginary restrictions then represent
every bounded complex functional by an actual complex measure.
-/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace NLS.Fourier
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

def positiveFunctionalCompact (g : C(X,ℝ) →ₚ[ℝ] ℝ) : C_c(X,ℝ) →ₚ[ℝ] ℝ where
  toFun f := g f.toContinuousMap
  map_add' _ _ := g.map_add _ _
  map_smul' c f := g.map_smul' c f.toContinuousMap
  monotone' := fun _ _ h => g.monotone h

theorem exists_signedMeasure_real_representation [T2Space X] [Nonempty X]
    (ell : C(X,ℝ) →L[ℝ] ℝ) :
    ∃ s : SignedMeasure X, ∀ f : C(X,ℝ), signedMeasureContinuousIntegral s (realContinuousTest f) = (ell f : ℂ) := by
  obtain ⟨g,h,hgh⟩ := exists_positive_decomposition ell
  let μ := RealRMK.rieszMeasure (positiveFunctionalCompact g)
  let ν := RealRMK.rieszMeasure (positiveFunctionalCompact h)
  refine ⟨μ.toSignedMeasure - ν.toSignedMeasure,fun f => ?_⟩
  rw [signedMeasureContinuousIntegral_eq_of_rep _ μ ν rfl]
  change (∫ x, (f x : ℂ) ∂μ) - (∫ x, (f x : ℂ) ∂ν) = _
  rw [integral_complex_ofReal,integral_complex_ofReal,← Complex.ofReal_sub]
  congr 1
  let fc : C_c(X,ℝ) := ⟨f,HasCompactSupport.of_compactSpace _⟩
  have hg : (∫ x, f x ∂μ) = g f := RealRMK.integral_rieszMeasure (positiveFunctionalCompact g) fc
  have hh : (∫ x, f x ∂ν) = h f := RealRMK.integral_rieszMeasure (positiveFunctionalCompact h) fc
  rw [hg,hh,← hgh]

def realContinuousTestCLM : C(X,ℝ) →L[ℝ] C(X,ℂ) :=
  let F : C(X,ℝ) →ₗ[ℝ] C(X,ℂ) := {
    toFun := realContinuousTest
    map_add' := by intro f g; ext x; simp [realContinuousTest]
    map_smul' := by intro c f; ext x; simp [realContinuousTest] }
  F.mkContinuous 1 (by
    intro f
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    change ‖(f x : ℂ)‖ ≤ ‖f‖
    simpa only [Complex.norm_real] using f.norm_coe_le_norm x)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
theorem complexFunctional_eq_of_real (F G : C(X,ℂ) →L[ℂ] ℂ)
    (h : ∀ f : C(X,ℝ), F (realContinuousTest f) = G (realContinuousTest f)) : F = G := by
  ext f
  let fr : C(X,ℝ) := ⟨fun x => (f x).re,by fun_prop⟩
  let fi : C(X,ℝ) := ⟨fun x => (f x).im,by fun_prop⟩
  have he : f = realContinuousTest fr + Complex.I • realContinuousTest fi := by
    ext x
    change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
    simpa only [mul_comm] using (Complex.re_add_im (f x)).symm
  rw [he,map_add,map_add,map_smul,map_smul,h fr,h fi]

theorem complexMeasureContinuousIntegral_surjective [T2Space X] [Nonempty X] :
    Function.Surjective (complexMeasureContinuousIntegral (X := X)) := by
  intro F
  let Fr := Complex.reCLM.comp ((F.restrictScalars ℝ).comp realContinuousTestCLM)
  let Fi := Complex.imCLM.comp ((F.restrictScalars ℝ).comp realContinuousTestCLM)
  obtain ⟨s,hs⟩ := exists_signedMeasure_real_representation Fr
  obtain ⟨t,ht⟩ := exists_signedMeasure_real_representation Fi
  refine ⟨s.toComplexMeasure t,?_⟩
  apply complexFunctional_eq_of_real
  intro f
  change signedMeasureContinuousIntegral s (realContinuousTest f) +
    Complex.I * signedMeasureContinuousIntegral t (realContinuousTest f) = _
  rw [hs,ht]
  change ((F (realContinuousTest f)).re : ℂ) + Complex.I * ((F (realContinuousTest f)).im : ℂ) = _
  simpa only [mul_comm] using Complex.re_add_im (F (realContinuousTest f))

end NLS.Fourier
