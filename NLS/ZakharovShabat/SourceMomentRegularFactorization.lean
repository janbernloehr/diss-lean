import NLS.ZakharovShabat.SourceAbelianMomentEvenNumerator
import NLS.ZakharovShabat.SourcePsiQuadraticRootOffset

/-! # Regular psi factors in the second-moment estimates

The diagonal numerator is i times the selected quotient. Off the diagonal,
filling the omitted root with its midpoint leaves the numerator unchanged
and identifies its scaled regular factor with the actual chi of Section 12.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The diagonal regular numerator is exactly i times the canonical
single-root quotient, including at zeros of either numerator. -/
theorem sourceMomentRegularNumerator_diagonal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) :
    sourceMomentRegularNumerator hp hp1 k k a ψ z =
      Complex.I * sourceSingleRootQuotientJointProduct hp hp1 k (z,(a,ψ)) := by
  unfold sourceMomentRegularNumerator sourcePsiCandidate sourceSingleRootQuotientJointProduct sourceStandardRootOmittedJointProduct
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring_nf
  simp only [Complex.inv_I]
  ring

/-- Deleting different numerator roots gives the same cross-multiplied
regular expression. This form is valid even at a root collision. -/
theorem sourceMomentRegularNumerator_change_index
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) :
    (displacedRoots a n-z)*sourceMomentRegularNumerator hp hp1 n k a ψ z =
      (displacedRoots a k-z)*sourceMomentRegularNumerator hp hp1 k k a ψ z := by
  unfold sourceMomentRegularNumerator
  rw [← mul_div_assoc,sourcePsiCandidate_change_deleted_index hp hp1 n k a z,mul_div_assoc]

/-- The regular moment numerator factors on the selected gap itself,
not only on the complement of all gaps. -/
theorem sourceMomentRegularNumerator_eq_gap_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (havoid : displacedRoots a n-z ≠ 0) :
    sourceMomentRegularNumerator hp hp1 n k a ψ z =
      (displacedRoots a k-z)*sourcePsiGapRegularFactor hp hp1 n k a ψ z := by
  have he := sourceMomentRegularNumerator_change_index hp hp1 n k a ψ z
  rw [sourceMomentRegularNumerator_diagonal] at he
  unfold sourcePsiGapRegularFactor
  apply (mul_left_cancel₀ havoid)
  calc
    (displacedRoots a n-z)*sourceMomentRegularNumerator hp hp1 n k a ψ z = _ := he
    _ = _ := by field_simp

/-- Filling the unused root leaves the entire regular numerator unchanged. -/
theorem sourceMomentRegularNumerator_fillDeletedRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) (a : DeletedCoeff p n)
    (ξ : ℂ) (ψ : CoeffPair p) (z : ℂ) :
    sourceMomentRegularNumerator hp hp1 n k (sourcePsiFillDeletedRoot n a ξ) ψ z =
      sourceMomentRegularNumerator hp hp1 n k (a : Coeff p) ψ z := by
  unfold sourceMomentRegularNumerator
  rw [sourcePsiCandidate_eq_of_off_index hp hp1 n z _ _
    (fun j hj => sourcePsiFillDeletedRoot_apply_other n j hj a ξ)]

/-- The scaled off-diagonal regular numerator uses exactly the chi
factor whose locally uniform estimates were established in Section 12. -/
theorem sourceMomentRegularNumerator_eq_midpointFilledFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) (hkn : k ≠ n) (a : DeletedCoeff p n)
    (ψ : CoeffPair p) (z : ℂ) (havoid : sourceStandardRootMidpoint hp hp1 ψ n-z ≠ 0) :
    (Real.pi:ℂ)*((n-k:ℤ):ℂ)*sourceMomentRegularNumerator hp hp1 n k (a : Coeff p) ψ z =
      (displacedRoots (a : Coeff p) k-z)*sourcePsiMidpointFilledRegularFactor hp hp1 n k a ψ z := by
  rw [← sourceMomentRegularNumerator_fillDeletedRoot hp hp1 n k a (sourceStandardRootMidpoint hp hp1 ψ n),
    sourceMomentRegularNumerator_eq_gap_factor hp hp1 n k _ ψ z
      (by simpa only [displacedRoots_sourcePsiFillDeletedRoot_same] using havoid),
    displacedRoots_sourcePsiFillDeletedRoot_other n k hkn]
  unfold sourcePsiMidpointFilledRegularFactor
  ring

end NLS.ZakharovShabat
