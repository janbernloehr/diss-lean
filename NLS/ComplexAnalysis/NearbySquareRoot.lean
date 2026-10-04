import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot
import Mathlib.Tactic.Linarith

/-! # A square root close to a prescribed value

Selecting the closer of the two roots gives a uniform square-root
modulus of continuity, including when the prescribed value is zero.
The selection itself is not asserted to be continuous or analytic.
-/
noncomputable section
namespace NLS.ComplexAnalysis

/-- Every complex number has a square root close to any prescribed
value, controlled by the error in its square. -/
theorem exists_nearby_squareRoot (a b : ℂ) :
    ∃ w : ℂ, w ^ 2 = b ∧ ‖w-a‖ ^ 2 ≤ ‖b-a^2‖ := by
  let w := Complex.sqrt b
  have hw : w ^ 2 = b := by
    have h := Complex.cpow_nat_inv_pow b (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [w,Complex.sqrt,one_div] using h
  have hprod : ‖w-a‖ * ‖w+a‖ = ‖b-a^2‖ := by
    rw [← norm_mul,show (w-a)*(w+a) = w^2-a^2 by ring,hw]
  by_cases h : ‖w-a‖ ≤ ‖w+a‖
  · exact ⟨w,hw,by nlinarith [norm_nonneg (w-a)]⟩
  · refine ⟨-w,by simpa using hw,?_⟩
    have hn : ‖-w-a‖ = ‖w+a‖ := by rw [show -w-a = -(w+a) by ring,norm_neg]
    rw [hn]
    nlinarith [norm_nonneg (w+a)]

end NLS.ComplexAnalysis
