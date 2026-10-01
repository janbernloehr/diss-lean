import NLS.ComplexAnalysis.MixedSpectralSourceDerivative

/-! # The actual differential of a moving spectral evaluation

A spectral family evaluated at a moving source coordinate has both its
fixed-parameter source differential and its spectral derivative multiplied
by the coordinate differential. The statement is an equality of full
continuous cotangents, without an implicit differentiability assumption.
-/

noncomputable section
namespace NLS.ComplexAnalysis
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem fderiv_moving_spectral_parameter
    (F : ℂ × A → ℂ) (μ : A → ℂ) (a : A)
    (hF : DifferentiableAt ℂ F (μ a,a)) (hμ : DifferentiableAt ℂ μ a) :
    fderiv ℂ (fun b : A => F (μ b,b)) a =
      fderiv ℂ (fun b : A => F (μ a,b)) a +
        deriv (fun z : ℂ => F (z,a)) (μ a) • fderiv ℂ μ a := by
  have hc := (hF.hasFDerivAt.comp a (f := fun b : A => (μ b,b))
    (hμ.hasFDerivAt.prodMk (hasFDerivAt_id a))).fderiv
  simp only [Function.comp_def] at hc
  rw [fderiv_source_section_eq_joint F (μ a) a hF,
    deriv_spectral_section_eq_fderiv F (μ a) a hF]
  ext h
  change (fderiv ℂ (fun b : A => F (μ b,b)) a) h = _
  rw [hc]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.inr_apply,
    add_apply,smul_apply,smul_eq_mul]
  have hp : ((fderiv ℂ μ a) h,h) =
      ((0 : ℂ),h) + ((fderiv ℂ μ a) h) • ((1 : ℂ),(0 : A)) := by
    ext <;> simp
  rw [hp,map_add,map_smul,smul_eq_mul]
  ring

end NLS.ComplexAnalysis
