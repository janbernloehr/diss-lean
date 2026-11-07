import NLS.Articles.KdVEstimates.DynamicalCorollaryEstimate
import NLS.KdV.KdVClassicalApproximation
import NLS.KdV.ClassicalKdVPhysicalAdapter
import NLS.KdV.KdVWeightedApproximation

noncomputable section
set_option autoImplicit false
open NLS.KdV
namespace NLS.Articles.KdVEstimates

/-- The actual Birkhoff actions are conserved for physical KdV solutions
defined by locally uniform classical approximation. The conservation law
is derived from the PDE, the Hill flux and L² continuity, not assumed. -/
theorem original_actions_conserved_of_kdv_solution (m : ℕ)
    (u : ℝ → RealHillWeightedPotential (hillIntegerWeight m))
    (hmean : ∀ t, (u t).val.val 0 = 0)
    (hu : IsKdVSolutionByClassicalApproximation
      (fun t => hillRealWeightedEmbedding (hillIntegerWeight m) (u t))) (s t : ℝ) (k : ℕ) :
    hillOriginalBirkhoffAction
        (hillOriginalWeightedMeanZeroSource (hillIntegerWeight m) (u t) (hmean t)) k =
      hillOriginalBirkhoffAction
        (hillOriginalWeightedMeanZeroSource (hillIntegerWeight m) (u s) (hmean s)) k := by
  rw [hillOriginalBirkhoffAction_eq_gapIntegral,hillOriginalBirkhoffAction_eq_gapIntegral]
  exact hu.physical_actions_conserved s t (k+1) (by omega)

/-- Corollary 1, first occurrence: the complete printed bound for the
classical-approximation KdV solution concept, with no conservation premise.
The constant precedes the initial data and time quantifiers. -/
theorem corollary1_dynamical (m : ℕ) (hm : 1 ≤ m) :
    ∃ α : ℝ, 0 < α ∧
      ∀ u : ℝ → RealHillWeightedPotential (hillIntegerWeight m),
      (u 0).val.val 0 = 0 →
      IsKdVSolutionByClassicalApproximation
        (fun t => hillRealWeightedEmbedding (hillIntegerWeight m) (u t)) →
      ∀ t, ‖(u t).val‖ ≤ α*(‖(u 0).val‖+
        (1+‖(hillRealNativeIntegerLower m (m-1) (by omega) (u 0)).val‖)^(m*m+m-1)*
          ‖(hillRealNativeIntegerLower m (m-1) (by omega) (u 0)).val‖) := by
  obtain ⟨α,hα,hbound⟩ := corollary1_dynamical_of_conserved_actions m hm
  refine ⟨α,hα,?_⟩
  intro u hzero hu
  have hmean : ∀ t, (u t).val.val 0 = 0 := by
    intro t
    have h := hu.mean_conserved 0 t
    simp only [hillRealWeightedEmbedding_zero_mode] at h
    exact h.trans hzero
  exact hbound u hmean (fun t k => original_actions_conserved_of_kdv_solution m u hmean hu 0 t k)

/-- In particular every genuine classical physical KdV trajectory in the
stated Sobolev domain satisfies the same corollary. -/
theorem corollary1_dynamical_classical (m : ℕ) (hm : 1 ≤ m) :
    ∃ α : ℝ, 0 < α ∧
      ∀ u : ℝ → RealHillWeightedPotential (hillIntegerWeight m),
      (u 0).val.val 0 = 0 →
      IsClassicalKdVTrajectory
        (fun t => hillRealWeightedEmbedding (hillIntegerWeight m) (u t)) →
      ∀ t, ‖(u t).val‖ ≤ α*(‖(u 0).val‖+
        (1+‖(hillRealNativeIntegerLower m (m-1) (by omega) (u 0)).val‖)^(m*m+m-1)*
          ‖(hillRealNativeIntegerLower m (m-1) (by omega) (u 0)).val‖) := by
  obtain ⟨α,hα,hbound⟩ := corollary1_dynamical m hm
  exact ⟨α,hα,fun u hzero hu => hbound u hzero hu.byClassicalApproximation⟩

end NLS.Articles.KdVEstimates
