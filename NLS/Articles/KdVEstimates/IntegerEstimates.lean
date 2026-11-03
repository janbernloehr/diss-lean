import NLS.KdV.HillForwardSobolevBound
import NLS.Articles.KdVEstimates.InverseIntegerEstimate

/-! # Both inequalities of Theorem2 in the exact native period-one Fourier Sobolev presentation. -/

noncomputable section
set_option autoImplicit false
namespace NLS.Articles.KdVEstimates
open NLS.KdV
theorem theorem2_forward_native (m : ℕ) (hm : 1 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : RealHillWeightedPotential (hillIntegerWeight m), p.val.val 0 = 0 →
      let b := hillRealNativeIntegerLower m (m-1) (by omega) p
      hillNativeActionMass m m p ≤ c^2*(‖p.val‖^2+(1+‖b.val‖)^(2*m)*‖b.val‖^2) := by
  obtain ⟨C,hC,hbound⟩ := exists_hillNativeForwardSobolevBound m hm
  refine ⟨C+1,by linarith,?_⟩
  intro p hmean
  apply (hbound p hmean).trans
  apply mul_le_mul_of_nonneg_right
  · nlinarith [sq_nonneg C]
  · positivity

theorem theorem2_native (m : ℕ) (hm : 1 ≤ m) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
      ∀ p : RealHillWeightedPotential (hillIntegerWeight m), p.val.val 0 = 0 →
      let b := hillRealNativeIntegerLower m (m-1) (by omega) p
      (hillNativeActionMass m m p ≤ c^2*(‖p.val‖^2+(1+‖b.val‖)^(2*m)*‖b.val‖^2)) ∧
      (‖p.val‖^2 ≤ d^2*(hillNativeActionMass m m p+
        (1+hillNativeActionMass m (m-1) p)^m*hillNativeActionMass m (m-1) p)) := by
  obtain ⟨c,hc,hforward⟩ := theorem2_forward_native m hm
  obtain ⟨d,hd,hinverse⟩ := theorem2_inverse_native m hm
  exact ⟨c,d,hc,hd,fun p hmean => ⟨hforward p hmean,hinverse p hmean⟩⟩

end NLS.Articles.KdVEstimates
