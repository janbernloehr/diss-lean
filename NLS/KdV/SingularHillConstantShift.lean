import NLS.KdV.SingularHillMiuraFactorization
import NLS.KdV.SingularHillAlgebraicMultiplicity

/-! Literal constant-potential translation on the original H1/H-minus-one
operator and every full physical root-chain level. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

theorem hminusOneProduct_constant (c : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    hminusOneProduct (l2OriginalHminus (lp.single 2 0 c)) f = c • singularHillDomainInclusion f := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  change (hminusOneProduct _ f).val (mode (-n)) = c*(singularHillDomainInclusion f).val (mode (-n))
  rw [hminusOneProduct_coefficient,singularHillDomainInclusion_coefficient]
  simp only [l2OriginalHminus_coefficient,lp.single_apply,Pi.single_apply,sub_eq_zero,
    ite_mul,zero_mul,tsum_ite_eq']

/-- Adding a constant potential adds exactly that scalar times the native domain inclusion. -/
theorem singularHillOperator_add_constant
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) :
    singularHillOperator (q+l2OriginalHminus (lp.single 2 0 c)) =
      singularHillOperator q+c • singularHillDomainInclusion := by
  ext f
  change singularHillLaplacian f+hminusOneProduct (q+l2OriginalHminus (lp.single 2 0 c)) f =
    singularHillLaplacian f+hminusOneProduct q f+c • singularHillDomainInclusion f
  rw [hminusOneProduct_add_left,hminusOneProduct_constant]
  abel

theorem singularHillPencil_add_constant
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c z : ℂ) :
    singularHillOperator (q+l2OriginalHminus (lp.single 2 0 c))-(z+c) • singularHillDomainInclusion =
      singularHillOperator q-z • singularHillDomainInclusion := by
  rw [singularHillOperator_add_constant,add_smul]
  abel

/-- The spectral translation preserves every actual finite physical root space. -/
theorem singularHillRootSpace_add_constant
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c z : ℂ) (n : ℕ) :
    singularHillRootSpace (q+l2OriginalHminus (lp.single 2 0 c)) (z+c) n =
      singularHillRootSpace q z n := by
  unfold singularHillRootSpace
  rw [singularHillPencil_add_constant]

theorem singularHillRootSpaceTop_add_constant
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c z : ℂ) :
    singularHillRootSpaceTop (q+l2OriginalHminus (lp.single 2 0 c)) (z+c) =
      singularHillRootSpaceTop q z := by
  unfold singularHillRootSpaceTop
  rw [singularHillPencil_add_constant]

/-- Actual full-domain algebraic multiplicity is invariant under the same translation. -/
theorem singularHillAlgebraicMultiplicity_add_constant
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c z : ℂ) :
    singularHillAlgebraicMultiplicity (q+l2OriginalHminus (lp.single 2 0 c)) (z+c) =
      singularHillAlgebraicMultiplicity q z := by
  change Module.finrank ℂ (singularHillRootSpaceTop _ _) = _
  rw [singularHillRootSpaceTop_add_constant]
  rfl

end NLS.KdV
