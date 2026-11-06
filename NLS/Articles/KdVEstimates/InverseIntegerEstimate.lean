import NLS.KdV.HillInverseSobolevBound

/-! # Theorem2(ii) in the exact native period-one Fourier Sobolev presentation. -/

noncomputable section
set_option autoImplicit false
namespace NLS.Articles.KdVEstimates
open NLS.KdV
theorem theorem2_inverse_native (m : ℕ) (hm : 1 ≤ m) :
    ∃ d : ℝ, 0 < d ∧ ∀ p : RealHillWeightedPotential (hillIntegerWeight m),
      p.val.val 0 = 0 → ‖p.val‖^2 ≤ d^2*(hillNativeActionMass m m p+
        (1+hillNativeActionMass m (m-1) p)^m*hillNativeActionMass m (m-1) p) := by
  obtain ⟨C,hC,hbound⟩ := exists_hillNativeInverseSobolevBound m hm
  refine ⟨C+1, by linarith, ?_⟩
  intro p hmean
  apply (hbound p hmean).trans
  apply mul_le_mul_of_nonneg_right
  · nlinarith [sq_nonneg C]
  · exact add_nonneg (hillNativeActionMass_nonneg m m p)
      (mul_nonneg (pow_nonneg (by linarith [hillNativeActionMass_nonneg m (m-1) p]) m)
        (hillNativeActionMass_nonneg m (m-1) p))

end NLS.Articles.KdVEstimates
