import NLS.ZakharovShabat.SourcePsiFreeOperator
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Stability of the free psi Jacobian

The free operator is `2 · id`, so its inverse has norm at most `1/2`.
Any bounded operator within distance two of it is therefore
invertible by a Neumann-series argument. Later spectral estimates can
use this as a concrete target for the nonfree Jacobian.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bound for the inverse free Jacobian on the deleted-coordinate
Banach space. -/
theorem norm_sourcePsiFreeJacobianInverseOperator_le (n : ℤ) :
    ‖sourcePsiFreeJacobianInverseOperator (p := p) n‖ ≤ 1 / 2 := by
  unfold sourcePsiFreeJacobianInverseOperator
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro a
  change ‖(2 : ℂ)⁻¹ • a‖ ≤ (1 / 2 : ℝ) * ‖a‖
  calc
    ‖(2 : ℂ)⁻¹ • a‖ ≤ ‖(2 : ℂ)⁻¹‖ * ‖a‖ := norm_smul_le _ _
    _ = (1 / 2 : ℝ) * ‖a‖ := by norm_num

/-- An operator less than distance two from the free diagonal
operator is invertible. -/
theorem isUnit_of_norm_sub_sourcePsiFreeJacobianOperator_lt_two
    (n : ℤ) (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (hQ : ‖Q - sourcePsiFreeJacobianOperator n‖ < 2) :
    IsUnit Q := by
  let J := sourcePsiFreeJacobianOperator (p := p) n
  let K := sourcePsiFreeJacobianInverseOperator (p := p) n
  have hJK : J * K = 1 := by
    apply ContinuousLinearMap.ext
    intro a
    exact sourcePsiFreeJacobianInverse_right n a
  have hJunit : IsUnit J := by
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    exact (sourcePsiFreeJacobianEquiv (p := p) n).bijective
  have hK : ‖K‖ ≤ 1 / 2 :=
    norm_sourcePsiFreeJacobianInverseOperator_le n
  have hsmall : ‖K * (J - Q)‖ < 1 := by
    calc
      ‖K * (J - Q)‖ ≤ ‖K‖ * ‖J - Q‖ := by
        change ‖K.comp (J - Q)‖ ≤ ‖K‖ * ‖J - Q‖
        exact K.opNorm_comp_le (J - Q)
      _ ≤ (1 / 2 : ℝ) * ‖J - Q‖ :=
        mul_le_mul_of_nonneg_right hK (norm_nonneg (J - Q))
      _ < (1 / 2 : ℝ) * 2 := by
        rw [show ‖J - Q‖ = ‖Q - J‖ from norm_sub_rev J Q]
        change ‖Q - J‖ < 2 at hQ
        exact mul_lt_mul_of_pos_left hQ (by norm_num)
      _ = 1 := by norm_num
  have hnear : IsUnit (1 - K * (J - Q)) := by
    have hsmall' :
        @norm (DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
          NormedRing.toNorm (K * (J - Q)) < 1 := by
      convert hsmall using 1
    convert (isUnit_one_sub_of_norm_lt_one hsmall') using 1
  have hfactor : Q = J * (1 - K * (J - Q)) := by
    rw [mul_sub, mul_one, ← mul_assoc, hJK, one_mul]
    abel
  rw [hfactor]
  exact hJunit.mul hnear

/-- The same quantitative condition gives a bijective bounded
Jacobian, the form needed for an implicit-function theorem. -/
theorem bijective_of_norm_sub_sourcePsiFreeJacobianOperator_lt_two
    (n : ℤ) (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (hQ : ‖Q - sourcePsiFreeJacobianOperator n‖ < 2) :
    Function.Bijective Q :=
  ContinuousLinearMap.isUnit_iff_bijective.mp
    (isUnit_of_norm_sub_sourcePsiFreeJacobianOperator_lt_two n Q hQ)

end NLS.ZakharovShabat
