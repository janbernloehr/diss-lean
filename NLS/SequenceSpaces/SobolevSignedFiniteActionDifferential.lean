import NLS.SequenceSpaces.SobolevSignedComplexActions
import NLS.SequenceSpaces.WeightedPositiveFiniteSums

/-! # The actual finite-support action differential in the original native norm

A closed action has zero first differential. Thus the complete Banach
differential at a finite-support real target is an exact finite sum in
positive raw unit directions; no infinite-series interchange is needed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS

/-- A true positive action vanishes exactly when its original signed coordinate does. -/
theorem sobolevSignedActionSequence_eq_zero_iff (r s : ℝ) (hrs : r=2*s)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) (n : ℕ+) :
    (sobolevSignedActionSequence r s hrs z).val (n : ℤ) = 0 ↔ z.val.val (n : ℤ) = 0 := by
  rw [sobolevSignedActionSequence_apply,if_pos (by exact_mod_cast n.pos : (0 : ℤ)<n),z.property.1 (n : ℤ)]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h|h
    · exact h
    · have hc := congrArg conj h
      simpa using hc
  · intro h
    rw [h,zero_mul]

/-- Every closed real signed coordinate has zero complete action differential,
even in arbitrary complex native directions. -/
theorem sobolevSignedActionJacobian_closed (r s : ℝ) (hrs : r=2*s)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s))
    (h : WeightedCoeff (Weight.sobolev s) 2) (n : ℕ+) (hz : z.val.val (n : ℤ) = 0) :
    (sobolevSignedActionJacobian r s hrs z.val h).val (n : ℤ) = 0 := by
  rw [sobolevSignedActionJacobian_apply,if_pos (by exact_mod_cast n.pos : (0 : ℤ)<n),
    z.property.1 (n : ℤ),hz,map_zero,zero_mul,mul_zero,add_zero]

/-- The ENTIRE weighted action differential at a real finite-support target
is the literal finite sum of its original positive coefficients. -/
theorem sobolevSignedActionJacobian_finite_sum (r s : ℝ) (hrs : r=2*s)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) (S : Finset ℕ+)
    (hz : ∀ n : ℕ+, n ∉ S → z.val.val (n : ℤ) = 0)
    (h : WeightedCoeff (Weight.sobolev s) 2) :
    sobolevSignedActionJacobian r s hrs z.val h = ∑ n ∈ S,
      (z.val.val n*h.val (-n)+h.val n*z.val.val (-n)) •
        WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1 := by
  have he := WeightedCoeff.eq_sum_positive_single_of_support (Weight.sobolev r) 1
    (sobolevSignedActionJacobian r s hrs z.val h) S
    (by intro j hj; rw [sobolevSignedActionJacobian_apply,if_neg (by omega)])
    (fun n hn => sobolevSignedActionJacobian_closed r s hrs z h n (hz n hn))
  rw [he]
  apply Finset.sum_congr rfl
  intro n _
  rw [sobolevSignedActionJacobian_apply,if_pos (by exact_mod_cast n.pos : (0 : ℤ)<n)]

/-- The same finite-sum identity holds for every actual real native variation. -/
theorem sobolevRealSignedActionJacobian_finite_sum (r s : ℝ) (hrs : r=2*s)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) (S : Finset ℕ+)
    (hz : ∀ n : ℕ+, n ∉ S → z.val.val (n : ℤ) = 0)
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    sobolevRealSignedActionJacobian r s hrs z h = ∑ n ∈ S,
      (z.val.val n*h.val.val (-n)+h.val.val n*z.val.val (-n)) •
        WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1 :=
  sobolevSignedActionJacobian_finite_sum r s hrs z S hz h.val

/-- Finite support of the actual action sequence suffices; no independent
support assumption on its square roots is required. -/
theorem sobolevRealSignedActionJacobian_finite_sum_of_actions (r s : ℝ) (hrs : r=2*s)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) (S : Finset ℕ+)
    (hz : ∀ n : ℕ+, n ∉ S → (sobolevSignedActionSequence r s hrs z).val (n : ℤ) = 0)
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    sobolevRealSignedActionJacobian r s hrs z h = ∑ n ∈ S,
      (z.val.val n*h.val.val (-n)+h.val.val n*z.val.val (-n)) •
        WeightedCoeff.single (Weight.sobolev r) (n : ℤ) 1 :=
  sobolevRealSignedActionJacobian_finite_sum r s hrs z S
    (fun n hn => (sobolevSignedActionSequence_eq_zero_iff r s hrs z n).mp (hz n hn)) h

end NLS
