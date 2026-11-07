import NLS.KdV.SingularDirichletPencil
import NLS.KdV.SingularHillSemibounded

/-! Complex Dirichlet energies obey the SAME original H-minus-one
sector bound, using only the full native weak eigen-equation. -/
noncomputable section
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The original energy proof needs only its scalar weak energy identity,
so it applies to genuine Dirichlet vectors without a periodic eigen-equation. -/
theorem singularHill_weak_energy_eigenvalue_norm_le
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) (hf0 : f ≠ 0)
    (hf : singularHillSesquilinear (singularHillOperator q f) f =
      z*singularHillSesquilinear (singularHillDomainInclusion f) f) :
    ‖z‖ ≤ 2*z.re+4*singularHillLowerBoundConstant ‖q‖ := by
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
    rw [hf,Complex.mul_re,singularHillDomainInclusion_energy_im,mul_zero,sub_zero] at h
    exact h
  have him : z.im*E = V.im := by
    have hi := congrArg Complex.im hf
    change (singularHillSesquilinear (singularHillLaplacian f+hminusOneMultiplication q f) f).im = _ at hi
    rw [singularHillSesquilinear_add_left,Complex.add_im,singularHillLaplacian_energy_im,
      zero_add,Complex.mul_im,singularHillDomainInclusion_energy_im,mul_zero,zero_add] at hi
    exact hi.symm
  have hab : |z.im| * E ≤ ‖V‖ := by
    rw [← abs_of_pos hE,← abs_mul,him]
    exact Complex.abs_im_le_norm V
  have hi : |z.im| ≤ z.re+2*C := by
    apply (mul_le_mul_iff_of_pos_right hE).mp
    nlinarith
  have hr : -C ≤ z.re := by
    have h := singularHill_form_lower_bound q f
    rw [hf,Complex.mul_re,singularHillDomainInclusion_energy_im,mul_zero,sub_zero] at h
    exact (mul_le_mul_iff_of_pos_right hE).mp h
  have hC : 0 ≤ C := singularHillLowerBoundConstant_nonneg _
  have hre : |z.re| ≤ z.re+2*C := by apply abs_le.mpr;constructor <;> linarith
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by dsimp only [C] at *;linarith)

/-- Every genuine native complex Dirichlet eigenvalue has the original
quartic H-minus-one sector bound, including central multiple eigenvalues. -/
theorem singularDirichlet_eigenvalue_norm_le
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) (g : UnitDirichletH1) (hg0 : g ≠ 0)
    (hg : singularDirichletOperator q g = z • singularDirichletDomainInclusion g) :
    ‖z‖ ≤ 2*z.re+4*singularHillLowerBoundConstant ‖q‖ := by
  apply singularHill_weak_energy_eigenvalue_norm_le q z (unitDirichletOriginalH1 g)
    (by intro he;apply hg0;apply unitDirichletOriginalH1_injective;simpa only [map_zero] using he)
  have he := congrArg (fun F : UnitDirichletHminus => F (unitDirichletConjugate g)) hg
  change singularHillPairing (singularHillOperator q (unitDirichletOriginalH1 g))
      (unitDirichletOriginalH1 (unitDirichletConjugate g)) =
    z*singularHillPairing (singularHillDomainInclusion (unitDirichletOriginalH1 g))
      (unitDirichletOriginalH1 (unitDirichletConjugate g)) at he
  rw [← unitDirichletOriginalH1_conjugate] at he
  exact he

end NLS.KdV
