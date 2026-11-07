import NLS.KdV.SingularHillSesquilinear
import NLS.KdV.SingularHillRootSpace
import NLS.FunctionalAnalysis.PencilRootSemisimple

/-!
# Spectral reality and semisimplicity on the full singular domain

Native real H-minus-one potentials have no nonzero associated vectors on the
unchanged original H1 domain. All actual root levels collapse to the physical
eigenspace. No spectral enumeration or endpoint regularity is assumed here.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
open NLS.FunctionalAnalysis

/-- The actual pencil has zero weak pairing against its own nonzero eigenvector. -/
theorem singularHillPencil_pair_eigenvector (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : q.val = q.val.conjugate) (z : ℂ) (f g : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : f ≠ 0) (he : singularHillOperator q f = z • singularHillDomainInclusion f) :
    singularHillSesquilinear (singularHillOperator q g-z • singularHillDomainInclusion g) f = 0 := by
  have hz := singularHill_eigenvalue_im_eq_zero q hq z f hf he
  have hstar : star z = z := by
    apply Complex.ext
    · simp only [Complex.star_def, Complex.conj_re]
    · simp only [Complex.star_def, Complex.conj_im, hz, neg_zero]
  rw [singularHillSesquilinear_sub_left, singularHillSesquilinear_smul_left,
    singularHillOperator_hermitian q hq g f, he, singularHillSesquilinear_smul_left,
    star_mul, hstar, ← singularHillDomainInclusion_hermitian]
  ring

/-- A nonzero actual eigenvector cannot have an associated vector on the full H1 domain. -/
theorem singularHill_no_associated_vector (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : q.val = q.val.conjugate) (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : f ≠ 0) (he : singularHillOperator q f = z • singularHillDomainInclusion f)
    (g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillOperator q g-z • singularHillDomainInclusion g ≠ singularHillDomainInclusion f := by
  intro hg
  have hzero := singularHillPencil_pair_eigenvector q hq z f g hf he
  rw [hg] at hzero
  have hpos := singularHillDomainInclusion_energy_pos f hf
  rw [hzero, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- Actual eigenvectors for distinct eigenvalues are orthogonal for the
original Fourier energy pairing. Zero vectors are allowed. -/
theorem singularHill_eigenvectors_orthogonal (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : q.val = q.val.conjugate) (z w : ℂ) (hzw : z ≠ w)
    (f g : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator q f = z • singularHillDomainInclusion f)
    (hg : singularHillOperator q g = w • singularHillDomainInclusion g) :
    singularHillSesquilinear (singularHillDomainInclusion f) g = 0 := by
  by_cases hg0 : g = 0
  · subst g
    simp only [singularHillSesquilinear, singularHillPairing, map_zero]
  have hw := singularHill_eigenvalue_im_eq_zero q hq w g hg0 hg
  have hstar : star w = w := by
    apply Complex.ext
    · simp only [Complex.star_def, Complex.conj_re]
    · simp only [Complex.star_def, Complex.conj_im, hw, neg_zero]
  have he := singularHillOperator_hermitian q hq f g
  rw [hf, hg, singularHillSesquilinear_smul_left, singularHillSesquilinear_smul_left,
    star_mul, hstar, ← singularHillDomainInclusion_hermitian] at he
  have hz : (z-w)*singularHillSesquilinear (singularHillDomainInclusion f) g = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hzw)

/-- The original domain eigenspace is linearly equivalent to its actual first root level. -/
def singularHillEigenspaceRootEquiv (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    singularHillEigenspace q z ≃ₗ[ℂ] singularHillRootSpace q z 1 :=
  pencilKerRootEquiv singularHillDomainInclusion.toLinearMap
    (singularHillOperator q-z • singularHillDomainInclusion).toLinearMap
      singularHillDomainInclusion_injective

/-- Every finite physical root level of a real singular potential lies in the actual eigenspace. -/
theorem singularHillRootSpace_le_one_of_real (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : q.val = q.val.conjugate) (z : ℂ) (n : ℕ) :
    singularHillRootSpace q z n ≤ singularHillRootSpace q z 1 := by
  apply pencilRootSpace_le_one_of_no_associated
  intro f g hf hg
  by_contra hf0
  exact singularHill_no_associated_vector q hq z f hf0 (sub_eq_zero.mp hf) g hg

/-- For native real singular potentials, the full actual algebraic root space
is the physical eigenspace, retaining every original domain requirement. -/
theorem singularHillRootSpaceTop_eq_one_of_real (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : q.val = q.val.conjugate) (z : ℂ) :
    singularHillRootSpaceTop q z = singularHillRootSpace q z 1 := by
  apply pencilRootSpaceTop_eq_one_of_no_associated
  intro f g hf hg
  by_contra hf0
  exact singularHill_no_associated_vector q hq z f hf0 (sub_eq_zero.mp hf) g hg

end NLS.KdV
