import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.SequenceSpaces.MeanZeroWeightedCoordinates

/-! # Exact signed action rotation generators in weighted Hilbert coordinates -/
noncomputable section
open Complex
namespace NLS.WeightedCoeff

def signedModeGenerator (w : Weight) (m : ℕ) : WeightedCoeff w 2 →L[ℂ] WeightedCoeff w 2 :=
  (evalCLM w 2 (m : ℤ)).smulRight (I • ofFinsupp w 2 (Finsupp.single (m : ℤ) 1)) -
    (evalCLM w 2 (-(m : ℤ))).smulRight (I • ofFinsupp w 2 (Finsupp.single (-(m : ℤ)) 1))

theorem signedModeGenerator_apply (w : Weight) (m : ℕ) (z : WeightedCoeff w 2) (j : ℤ) :
    (signedModeGenerator w m z).val j =
      (if j = (m : ℤ) then I*z.val j else 0) - (if j = -(m : ℤ) then I*z.val j else 0) := by
  change z.val (m : ℤ)*(I*(Finsupp.single (m : ℤ) (1 : ℂ)) j) -
    z.val (-(m : ℤ))*(I*(Finsupp.single (-(m : ℤ)) (1 : ℂ)) j) = _
  have he (k : ℤ) : z.val k*(I*(Finsupp.single k (1 : ℂ)) j) =
      if j = k then I*z.val j else 0 := by
    by_cases hj : j = k
    · subst j
      simp only [Finsupp.single_eq_same,mul_one,if_true,mul_comm]
    · simp only [Finsupp.single_apply,if_neg hj,if_neg (Ne.symm hj),mul_zero]
  exact congrArg₂ (fun a b : ℂ => a-b) (he _) (he _)

theorem signedModeGenerator_zero_mode (w : Weight) (m : ℕ) (hm : 1 ≤ m) (z : WeightedCoeff w 2) :
    (signedModeGenerator w m z).val 0 = 0 := by
  rw [signedModeGenerator_apply]
  simp only [show (0 : ℤ) ≠ (m : ℤ) by omega,show (0 : ℤ) ≠ -(m : ℤ) by omega,if_false,sub_self]

def meanZeroSignedModeGenerator (w : Weight) (m : ℕ) : DeletedCoeff 2 0 →L[ℂ] DeletedCoeff 2 0 :=
  (meanZeroWeightedProjectionCLM w).comp ((signedModeGenerator w m).comp (meanZeroWeightedLiftCLM w))

theorem meanZeroSignedModeGenerator_projection (w : Weight) (m : ℕ) (z : WeightedCoeff w 2)
    (hz : z.val 0 = 0) :
    meanZeroSignedModeGenerator w m (meanZeroWeightedProjectionCLM w z) =
      meanZeroWeightedProjectionCLM w (signedModeGenerator w m z) := by
  change meanZeroWeightedProjectionCLM w (signedModeGenerator w m
    (meanZeroWeightedLiftCLM w (meanZeroWeightedProjectionCLM w z))) = _
  rw [meanZeroWeightedLift_projection w z hz]

end NLS.WeightedCoeff
