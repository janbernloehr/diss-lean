import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalClassicalRoughSolution
import NLS.Articles.KdVPseudomeasures.OriginalHillEndpointCanonicalTrajectories

/-! Original Theorem 1.1 in its literal physical endpoint space and
Wiener weak-star topology. The solution is the UNIQUE original rough
curve characterized by EVERY jointly smooth classical approximation;
that characterization has a constructed approximating family for
every original rough initial potential. -/
noncomputable section
open Set NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem admissiblePredualOrder_neg_of_sourceRange (s : ℝ)
    (hs : -(1 / 2 : ℝ) < s ∧ s ≤ 0) : AdmissiblePredualOrder (-s) :=
  ⟨by linarith [hs.2], by linarith [hs.1]⟩

def sourceTheorem1_1Statement : Prop :=
  ∀ (s : ℝ) (hs : -(1 / 2 : ℝ) < s ∧ s ≤ 0) (q : Potential (-s)),
    let hr := admissiblePredualOrder_neg_of_sourceRange s hs
    ∃ γ : ℝ → WeakStarPotential (-s), γ 0 = ⟨q⟩ ∧
      OriginalKdVSolutionByClassicalApproximation (sourceOriginalPotential (-s) hr q)
        (fun t => sourceOriginalPotential (-s) hr (γ t).toPotential) ∧
      (∀ t, sourceOriginalPotential (-s) hr (γ t).toPotential =
        hillOriginalCanonicalKdVFlow (sourceOriginalPotential (-s) hr q) t) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖(γ t).toPotential.val‖ ≤ C) ∧
      Continuous γ

theorem sourceTheorem1_1 : sourceTheorem1_1Statement := by
  intro s hs q
  let hr := admissiblePredualOrder_neg_of_sourceRange s hs
  refine ⟨hillEndpointWeakStarKdVFlow (-s) hr ⟨q⟩, ?_, ?_, ?_, ?_, ?_⟩
  · change (⟨hillEndpointCanonicalKdVFlow (-s) hr q 0⟩ : WeakStarPotential (-s)) = ⟨q⟩
    rw [hillEndpointCanonicalKdVFlow_zero]
  · have he : (fun t => sourceOriginalPotential (-s) hr
        (hillEndpointWeakStarKdVFlow (-s) hr ⟨q⟩ t).toPotential) =
        hillOriginalCanonicalKdVFlow (sourceOriginalPotential (-s) hr q) :=
      funext (fun t => hillEndpointCanonicalKdVFlow_original (-s) hr q t)
    rw [he]
    exact hillOriginalCanonicalFlow_is_solutionByClassicalApproximation _
  · intro t
    exact hillEndpointCanonicalKdVFlow_original (-s) hr q t
  · exact exists_uniform_norm_bound_hillEndpointCanonicalKdVFlow (-s) hr q
  · exact continuous_hillEndpointWeakStarKdVFlow_time (-s) hr ⟨q⟩

end NLS.Articles.KdVPseudomeasures
