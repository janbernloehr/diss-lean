import NLS.KdV.SingularHillEnergy

/-!
# A lower quadratic-form and eigenvalue bound on the original singular domain

Every original complex H-minus-one potential has this real-part form bound on
its entire original H1 domain. Reality is not needed until full real spectral
consequences. The explicit constant is quartic in the genuine H-minus-one norm.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- An explicit nonnegative lower-bound constant in the original potential norm. -/
def singularHillLowerBoundConstant (R : ℝ) : ℝ := 1+93312*R^4

theorem singularHillLowerBoundConstant_nonneg (R : ℝ) : 0 ≤ singularHillLowerBoundConstant R := by
  unfold singularHillLowerBoundConstant
  positivity

theorem singularHillLowerBoundConstant_mono {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) :
    singularHillLowerBoundConstant R ≤ singularHillLowerBoundConstant S := by
  unfold singularHillLowerBoundConstant
  have hp := pow_le_pow_left₀ hR hRS 4
  nlinarith


/-- The native singular multiplication form has an explicit quarter-H1 estimate. -/
theorem norm_singularHillMultiplication_form_le (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    ‖singularHillSesquilinear (hminusOneMultiplication q f) f‖ ≤
      ‖f‖^2/4+93312*‖q‖^4*‖h1L2Coefficients f‖^2 :=
  norm_hminusOne_quadratic_le_quarter q f

/-- The full original singular weak form retains half the positive free energy. -/
theorem singularHill_form_coercive_lower_bound (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    (1/2:ℝ)*(singularHillSesquilinear (singularHillLaplacian f) f).re -
      singularHillLowerBoundConstant ‖q‖*(singularHillSesquilinear (singularHillDomainInclusion f) f).re ≤
        (singularHillSesquilinear (singularHillOperator q f) f).re := by
  have hv := norm_singularHillMultiplication_form_le q f
  have hRe := (abs_le.mp (Complex.abs_re_le_norm
    (singularHillSesquilinear (hminusOneMultiplication q f) f))).1
  have hH := singularHill_domain_norm_sq_le_energy f
  have hJ : (singularHillSesquilinear (singularHillDomainInclusion f) f).re = ‖h1L2Coefficients f‖^2 := by
    rw [singularHillDomainInclusion_energy_eq_norm_sq,Complex.ofReal_re]
  change _ ≤ (singularHillSesquilinear (singularHillLaplacian f+hminusOneMultiplication q f) f).re
  rw [singularHillSesquilinear_add_left,Complex.add_re]
  unfold singularHillLowerBoundConstant
  rw [hJ] at hH ⊢
  nlinarith [sq_nonneg ‖h1L2Coefficients f‖]

/-- Every original complex singular potential has a lower real-part form bound. -/
theorem singularHill_form_lower_bound (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    -singularHillLowerBoundConstant ‖q‖*(singularHillSesquilinear (singularHillDomainInclusion f) f).re ≤
      (singularHillSesquilinear (singularHillOperator q f) f).re := by
  have h := singularHill_form_coercive_lower_bound q f
  have hD := singularHillLaplacian_energy_nonneg f
  linarith

/-- Every actual eigenvalue on the full original domain lies in an explicit right half-plane. -/
theorem singularHill_eigenvalue_re_lower_bound (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2) (hf0 : f ≠ 0)
    (hf : singularHillOperator q f = z • singularHillDomainInclusion f) :
    -singularHillLowerBoundConstant ‖q‖ ≤ z.re := by
  have h := singularHill_form_lower_bound q f
  rw [hf,singularHillSesquilinear_smul_left,Complex.mul_re,
    singularHillDomainInclusion_energy_im,mul_zero,sub_zero] at h
  exact (mul_le_mul_iff_of_pos_right (singularHillDomainInclusion_energy_pos f hf0)).mp h

/-- One original H-minus-one norm-ball bound works for every actual eigenvalue. -/
theorem singularHill_eigenvalue_re_lower_bound_of_norm_le (R : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (hq : ‖q‖ ≤ R)
    (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2) (hf0 : f ≠ 0)
    (hf : singularHillOperator q f = z • singularHillDomainInclusion f) :
    -singularHillLowerBoundConstant R ≤ z.re :=
  (neg_le_neg (singularHillLowerBoundConstant_mono (norm_nonneg q) hq)).trans
    (singularHill_eigenvalue_re_lower_bound q z f hf0 hf)

/-- The actual free quadratic form has zero imaginary part. -/
theorem singularHillLaplacian_energy_im (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    (singularHillSesquilinear (singularHillLaplacian f) f).im = 0 := by
  rw [singularHillLaplacian_energy_eq_norm_sq,Complex.ofReal_im]

/-- Actual singular eigenvalues lie in a norm-controlled sector, also for complex potentials. -/
theorem singularHill_eigenvalue_abs_im_le (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2) (hf0 : f ≠ 0)
    (hf : singularHillOperator q f = z • singularHillDomainInclusion f) :
    |z.im| ≤ z.re+2*singularHillLowerBoundConstant ‖q‖ := by
  let E := (singularHillSesquilinear (singularHillDomainInclusion f) f).re
  let D := (singularHillSesquilinear (singularHillLaplacian f) f).re
  let C := singularHillLowerBoundConstant ‖q‖
  let V := singularHillSesquilinear (hminusOneMultiplication q f) f
  have hE : 0 < E := singularHillDomainInclusion_energy_pos f hf0
  have hJ : ‖h1L2Coefficients f‖^2 = E := by
    dsimp [E]
    rw [singularHillDomainInclusion_energy_eq_norm_sq,Complex.ofReal_re]
  have hH : ‖f‖^2 ≤ 2*(E+D) := singularHill_domain_norm_sq_le_energy f
  have hV : ‖V‖ ≤ ‖f‖^2/4+(C-1)*E := by
    have h := norm_singularHillMultiplication_form_le q f
    rw [hJ] at h
    simpa only [C,singularHillLowerBoundConstant,add_sub_cancel_left] using h
  have hco : (1/2:ℝ)*D-C*E ≤ z.re*E := by
    have h := singularHill_form_coercive_lower_bound q f
    rw [hf,singularHillSesquilinear_smul_left,Complex.mul_re,
      singularHillDomainInclusion_energy_im,mul_zero,sub_zero] at h
    exact h
  have him : z.im*E = V.im := by
    have h : singularHillSesquilinear (singularHillOperator q f) f =
        z*singularHillSesquilinear (singularHillDomainInclusion f) f := by
      rw [hf,singularHillSesquilinear_smul_left]
    have hi := congrArg Complex.im h
    change (singularHillSesquilinear (singularHillLaplacian f+hminusOneMultiplication q f) f).im = _ at hi
    rw [singularHillSesquilinear_add_left,Complex.add_im,singularHillLaplacian_energy_im,
      zero_add,Complex.mul_im,singularHillDomainInclusion_energy_im,mul_zero,zero_add] at hi
    exact hi.symm
  have hab : |z.im| * E ≤ ‖V‖ := by
    rw [← abs_of_pos hE,← abs_mul,him]
    exact Complex.abs_im_le_norm V
  apply (mul_le_mul_iff_of_pos_right hE).mp
  nlinarith

/-- The entire actual eigenvalue has a bound on each left real half-plane. -/
theorem singularHill_eigenvalue_norm_le (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2) (hf0 : f ≠ 0)
    (hf : singularHillOperator q f = z • singularHillDomainInclusion f) :
    ‖z‖ ≤ 2*z.re+4*singularHillLowerBoundConstant ‖q‖ := by
  have hr := singularHill_eigenvalue_re_lower_bound q z f hf0 hf
  have hi := singularHill_eigenvalue_abs_im_le q z f hf0 hf
  have hC := singularHillLowerBoundConstant_nonneg ‖q‖
  have hab : |z.re| ≤ z.re+2*singularHillLowerBoundConstant ‖q‖ := by
    apply abs_le.mpr
    constructor <;> linarith
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)

end NLS.KdV
