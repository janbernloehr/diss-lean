import NLS.Fourier.PeriodicSobolevConjugation
import NLS.KdV.SingularHillBilinear

/-!
# The Hermitian weak form of the original singular Hill operator

The domain is the full original period-two H1 space and the potential is any
original H-minus-one distribution. Reality is native distributional reality.
The sesquilinear form is linear in its first argument, and the domain inclusion
has strictly positive quadratic energy on every nonzero original H1 vector.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- Native conjugation commutes with the unchanged original domain inclusion. -/
theorem singularHillDomainInclusion_conjugation (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    sobolevConjugation (-1) 2 (singularHillDomainInclusion f) =
      singularHillDomainInclusion (sobolevConjugation 1 2 f) := by
  apply Subtype.ext
  simp only [sobolevConjugation_val, singularHillDomainInclusion_val]

/-- Native conjugation commutes with the original free singular operator. -/
theorem singularHillLaplacian_conjugation (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    sobolevConjugation (-1) 2 (singularHillLaplacian f) =
      singularHillLaplacian (sobolevConjugation 1 2 f) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  have hc := singularHillLaplacian_coefficient f (-k)
  simp only [neg_neg] at hc
  rw [sobolevConjugation_coefficient, hc, singularHillLaplacian_coefficient,
    sobolevConjugation_coefficient, star_mul, freeHillValue_neg]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

/-- Physical conjugation covaries with multiplication by the conjugated potential. -/
theorem singularHillOperator_conjugation (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    sobolevConjugation (-1) 2 (singularHillOperator q f) =
      singularHillOperator (sobolevConjugation (-1) 2 q) (sobolevConjugation 1 2 f) := by
  change sobolevConjugation (-1) 2 (singularHillLaplacian f + hminusOneProduct q f) =
    singularHillLaplacian (sobolevConjugation 1 2 f) +
      hminusOneProduct (sobolevConjugation (-1) 2 q) (sobolevConjugation 1 2 f)
  rw [map_add, singularHillLaplacian_conjugation, hminusOneProduct_conjugation]

/-- The full original H-minus-one/H1 pairing, linear in its first argument. -/
def singularHillSesquilinear (v : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) : ℂ :=
  singularHillPairing v (sobolevConjugation 1 2 f)

/-- Original Fourier coefficients give the actual normalized sesquilinear form. -/
theorem singularHillSesquilinear_eq_tsum (v : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillSesquilinear v f = ∑' n : ℤ, star (f.val (mode n))*v.val (mode n) := by
  simp only [singularHillSesquilinear, singularHillPairing, sobolevDualIsometry_apply,
    sobolevConjugation_coefficient]

/-- The physical Fourier expression is absolutely convergent on the full original domain. -/
theorem summable_norm_singularHillSesquilinear (v : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    Summable (fun n : ℤ => ‖star (f.val (mode n))*v.val (mode n)‖) := by
  simpa only [sobolevConjugation_coefficient] using
    sobolevDualIsometry_summable 1 v
      (sobolevConjugation 1 2 f)

theorem singularHillSesquilinear_add_left (a b : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillSesquilinear (a+b) f = singularHillSesquilinear a f + singularHillSesquilinear b f :=
  singularHillPairing_add_left a b _

theorem singularHillSesquilinear_smul_left (c : ℂ) (v : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillSesquilinear (c • v) f = c * singularHillSesquilinear v f :=
  singularHillPairing_smul_left c v _

theorem singularHillSesquilinear_sub_left (a b : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillSesquilinear (a-b) f = singularHillSesquilinear a f - singularHillSesquilinear b f := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ b, singularHillSesquilinear_add_left,
    singularHillSesquilinear_smul_left]
  ring

/-- One-sided conjugation of the original bilinear form gives the Hermitian weak form. -/
theorem singularHillPairing_conjugate_left (v : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (sobolevConjugation (-1) 2 v) f = star (singularHillSesquilinear v f) :=
  sobolevDualIsometry_conjugate_left 1 (by norm_num) v f

/-- The actual original domain inclusion is Hermitian. -/
theorem singularHillDomainInclusion_hermitian (f g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillSesquilinear (singularHillDomainInclusion f) g =
      star (singularHillSesquilinear (singularHillDomainInclusion g) f) := by
  change singularHillPairing (singularHillDomainInclusion f) (sobolevConjugation 1 2 g) = _
  rw [singularHillDomainInclusion_bilinear, ← singularHillDomainInclusion_conjugation,
    singularHillPairing_conjugate_left]

/-- Every native real H-minus-one potential has a Hermitian weak form on the
full original H1 domain, with no endpoint or mean-zero premise. -/
theorem singularHillOperator_hermitian (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : q.val = q.val.conjugate) (f g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillSesquilinear (singularHillOperator q f) g =
      star (singularHillSesquilinear (singularHillOperator q g) f) := by
  have hq' : sobolevConjugation (-1) 2 q = q := Subtype.ext hq.symm
  have hc := singularHillOperator_conjugation q g
  rw [hq'] at hc
  change singularHillPairing (singularHillOperator q f) (sobolevConjugation 1 2 g) = _
  rw [singularHillOperator_bilinear, ← hc, singularHillPairing_conjugate_left]

/-- The domain inclusion's quadratic form is the exact squared Fourier energy. -/
theorem singularHillDomainInclusion_energy (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillSesquilinear (singularHillDomainInclusion f) f =
      ((∑' n : ℤ, Complex.normSq (f.val (mode n)) : ℝ) : ℂ) := by
  rw [singularHillSesquilinear_eq_tsum, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [singularHillDomainInclusion_val, Complex.star_def, mul_comm, Complex.mul_conj]

/-- The original Fourier energy is summable for every H1 domain vector. -/
theorem summable_singularHillDomainInclusion_energy (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    Summable (fun n : ℤ => Complex.normSq (f.val (mode n))) := by
  have hs := (summable_norm_singularHillSesquilinear (singularHillDomainInclusion f) f).of_norm
  have he : (fun n : ℤ => star (f.val (mode n)) *
      (singularHillDomainInclusion f).val (mode n)) =
      (fun n : ℤ => (Complex.normSq (f.val (mode n)) : ℂ)) := by
    funext n
    rw [singularHillDomainInclusion_val, Complex.star_def, mul_comm, Complex.mul_conj]
  rw [he] at hs
  exact Complex.summable_ofReal.mp hs

/-- Nonzero original H1 vectors have strictly positive domain energy. -/
theorem singularHillDomainInclusion_energy_pos (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : f ≠ 0) : 0 < (singularHillSesquilinear (singularHillDomainInclusion f) f).re := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, f.val (mode n) ≠ 0 := by
    contrapose! hf
    apply Subtype.ext
    apply Distribution.ext_coefficients
    intro k
    change f.val (mode (-k)) = 0
    exact hf (-k)
  rw [singularHillDomainInclusion_energy, Complex.ofReal_re]
  exact (summable_singularHillDomainInclusion_energy f).tsum_pos
    (fun _ => Complex.normSq_nonneg _) n (Complex.normSq_pos.mpr hn)

/-- The domain energy is real on the original domain. -/
theorem singularHillDomainInclusion_energy_im (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    (singularHillSesquilinear (singularHillDomainInclusion f) f).im = 0 := by
  rw [singularHillDomainInclusion_energy, Complex.ofReal_im]

/-- Native real singular potentials have real quadratic weak forms. -/
theorem singularHillOperator_energy_im (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : q.val = q.val.conjugate) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    (singularHillSesquilinear (singularHillOperator q f) f).im = 0 := by
  have he := congrArg Complex.im (singularHillOperator_hermitian q hq f f)
  simp only [Complex.star_def, Complex.conj_im] at he
  linarith

/-- Every actual eigenvalue of an arbitrary native real H-minus-one singular
potential is real, using the entire original H1 domain. -/
theorem singularHill_eigenvalue_im_eq_zero (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : q.val = q.val.conjugate) (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : f ≠ 0) (he : singularHillOperator q f = z • singularHillDomainInclusion f) :
    z.im = 0 := by
  have him := singularHillOperator_energy_im q hq f
  rw [he, singularHillSesquilinear_smul_left, Complex.mul_im,
    singularHillDomainInclusion_energy_im, mul_zero, zero_add] at him
  exact (mul_eq_zero.mp him).resolve_right
    (ne_of_gt (singularHillDomainInclusion_energy_pos f hf))

end NLS.KdV
