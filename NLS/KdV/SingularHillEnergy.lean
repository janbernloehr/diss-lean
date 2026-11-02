import NLS.KdV.SingularHillSesquilinear
import NLS.Fourier.PeriodicH1FormBound

/-!
# Exact original free and base energies of the singular Hill domain

All Fourier norms are the normalized original ones. The positive free symbol
pi^2*k^2 is retained. The entire original H1 norm is controlled by the sum of
the original L2 and free quadratic energies.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The same actual weak form in the original negative-test Fourier indices. -/
theorem singularHillSesquilinear_eq_tsum_neg (v : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillSesquilinear v f = ∑' k : ℤ, star (f.val (mode (-k)))*v.val (mode (-k)) := by
  rw [singularHillSesquilinear_eq_tsum]
  simpa only [Equiv.neg_apply] using
    ((Equiv.neg ℤ).tsum_eq (fun k : ℤ => star (f.val (mode k))*v.val (mode k))).symm

/-- Exact squared L2 energy of the entire original H1 domain element. -/
theorem h1L2Coefficients_norm_sq_eq_tsum (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    ‖h1L2Coefficients f‖^2 = ∑' k : ℤ, Complex.normSq (f.val (mode (-k))) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,h1L2Coefficients_apply,
    Complex.normSq_eq_norm_sq] using
    (lp.hasSum_norm (p := 2) (by norm_num) (h1L2Coefficients f)).tsum_eq.symm

/-- The actual domain-inclusion form is exactly the original squared L2 norm. -/
theorem singularHillDomainInclusion_energy_eq_norm_sq (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillSesquilinear (singularHillDomainInclusion f) f = ((‖h1L2Coefficients f‖^2:ℝ):ℂ) := by
  rw [h1L2Coefficients_norm_sq_eq_tsum,Complex.ofReal_tsum,singularHillSesquilinear_eq_tsum_neg]
  apply tsum_congr
  intro k
  rw [singularHillDomainInclusion_val,Complex.star_def,mul_comm,Complex.mul_conj]

/-- The genuine period-two derivative coefficients of the full original H1 vector. -/
def singularHillDerivativeCoefficients (f : FourierLebesgueSpace (2:ℝ) 1 2) : Coeff 2 :=
  NLS.ZakharovShabat.derivative (sobolevCoefficients 1 2 f)

@[simp] theorem singularHillDerivativeCoefficients_apply
    (f : FourierLebesgueSpace (2:ℝ) 1 2) (k : ℤ) :
    singularHillDerivativeCoefficients f k = Complex.I*(Real.pi:ℂ)*k*f.val (mode (-k)) := by
  simp only [singularHillDerivativeCoefficients,NLS.ZakharovShabat.derivative_apply,sobolevCoefficients_apply]

/-- The actual free weak form is precisely the squared original derivative norm. -/
theorem singularHillLaplacian_energy_eq_norm_sq (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillSesquilinear (singularHillLaplacian f) f = ((‖singularHillDerivativeCoefficients f‖^2:ℝ):ℂ) := by
  have hn : ‖singularHillDerivativeCoefficients f‖^2 =
      ∑' k : ℤ, ‖singularHillDerivativeCoefficients f k‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.hasSum_norm (p := 2) (by norm_num) (singularHillDerivativeCoefficients f)).tsum_eq.symm
  rw [hn,Complex.ofReal_tsum,singularHillSesquilinear_eq_tsum_neg]
  apply tsum_congr
  intro k
  rw [singularHillLaplacian_coefficient]
  have he : star (f.val (mode (-k)))*((freeHillValue k:ℂ)*f.val (mode (-k))) =
      (freeHillValue k:ℂ)*(Complex.normSq (f.val (mode (-k))):ℂ) := by
    rw [Complex.star_def,← Complex.mul_conj]
    ring
  rw [he,singularHillDerivativeCoefficients_apply]
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,Complex.norm_intCast,mul_pow,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.normSq_eq_norm_sq,freeHillValue,sq_abs]

/-- The actual free quadratic energy is nonnegative. -/
theorem singularHillLaplacian_energy_nonneg (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    0 ≤ (singularHillSesquilinear (singularHillLaplacian f) f).re := by
  rw [singularHillLaplacian_energy_eq_norm_sq,Complex.ofReal_re]
  positivity

/-- The original H1 norm is bounded by the original L2 and derivative graph norm. -/
theorem singularHill_domain_norm_le_graph (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    ‖f‖ ≤ ‖h1L2Coefficients f‖+‖singularHillDerivativeCoefficients f‖ := by
  have he : NLS.ZakharovShabat.scalarInclusion (sobolevCoefficients 1 2 f) = h1L2Coefficients f := by
    ext k
    simp only [NLS.ZakharovShabat.scalarInclusion_apply,sobolevCoefficients_apply,h1L2Coefficients_apply]
  have h := WeightedCoeff.norm_sobolev_le_base_add_derivative (sobolevCoefficients 1 2 f)
  rw [he,LinearIsometryEquiv.norm_map] at h
  have hp : Real.pi⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  change ‖f‖ ≤ ‖h1L2Coefficients f‖+Real.pi⁻¹*‖singularHillDerivativeCoefficients f‖ at h
  have hd : Real.pi⁻¹*‖singularHillDerivativeCoefficients f‖ ≤ ‖singularHillDerivativeCoefficients f‖ := by
    nlinarith [norm_nonneg (singularHillDerivativeCoefficients f)]
  linarith


/-- The full original H1 norm squared is controlled by twice the two actual quadratic energies. -/
theorem singularHill_domain_norm_sq_le_energy (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    ‖f‖^2 ≤ 2*((singularHillSesquilinear (singularHillDomainInclusion f) f).re +
      (singularHillSesquilinear (singularHillLaplacian f) f).re) := by
  rw [singularHillDomainInclusion_energy_eq_norm_sq,singularHillLaplacian_energy_eq_norm_sq,
    Complex.ofReal_re,Complex.ofReal_re]
  have h := pow_le_pow_left₀ (norm_nonneg f) (singularHill_domain_norm_le_graph f) 2
  nlinarith [sq_nonneg (‖h1L2Coefficients f‖-‖singularHillDerivativeCoefficients f‖)]

end NLS.KdV
