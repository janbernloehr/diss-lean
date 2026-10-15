import NLS.ZakharovShabat.SourceH1HigherActionEstimates
import NLS.ZakharovShabat.SourceSobolevActionEstimate
import NLS.ZakharovShabat.SourcePiSobolevCoordinates
import NLS.ZakharovShabat.SourceSection23Actions
import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic

/-! # Summed original action estimates with the physical Hamiltonian sign -/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- The corrected Lemma 26.2 on every original real Hᵐ source, with the stronger half-mass remainder. -/
theorem sourceSection26_action_estimate_half_mass (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
    let P := ‖sourcePiSobolevCoordinates m 1 hm a.val‖
    Summable (sourceIndexedWeightedActionTerm ψ m) ∧
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ψ m n) ≤
        (1+16*Real.pi)^(2*m)*(1+P)^(4*m)*(‖ψ.val‖^2/2)+
          2^m*(sobolevOddHamiltonian m hm a.val).re := by
  have he (ψ : realTypeSourceSubmodule 2) : sourceIndexedWeightedActionTerm ψ m =
      sourceWeightedActionTerm ψ m := funext (sourceIndexedWeightedActionTerm_eq ψ m)
  simpa only [he, norm_normalizedWeightedPeriodOne] using
    sourceWeightedAction_summable_and_le_half_mass m hm a
      (normalizedWeightedPeriodOne _ (sourcePiSobolevCoordinates m 1 hm a.val))
      (weightedBaseToPair_sourcePiSobolevOne m hm a.val)

/-- The corrected estimate with the full printed mass remainder and a positive Hamiltonian term. -/
theorem sourceSection26_action_estimate (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
    (∑' n : ℤ, sourceIndexedWeightedActionTerm ψ m n) ≤
      (1+16*Real.pi)^(2*m)*(1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(4*m)*‖ψ.val‖^2+
        2^m*(sobolevOddHamiltonian m hm a.val).re := by
  simpa only [sourceIndexedWeightedActionTerm_eq,norm_normalizedWeightedPeriodOne] using
    sourceWeightedAction_le_mass m hm a
      (normalizedWeightedPeriodOne _ (sourcePiSobolevCoordinates m 1 hm a.val))
      (weightedBaseToPair_sourcePiSobolevOne m hm a.val)

/-- At odd m the literal printed sign is positive, so the original statement is valid. -/
theorem sourceSection26_printed_estimate_of_odd (m : ℕ) (hm : 1 ≤ m) (hodd : Odd m)
    (a : realTypeHigherSobolevSourceLocus m) :
    let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
    (∑' n : ℤ, sourceIndexedWeightedActionTerm ψ m n) ≤
      (1+16*Real.pi)^(2*m)*(1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(4*m)*‖ψ.val‖^2+
        (-1:ℝ)^(m+1)*2^m*(sobolevOddHamiltonian m hm a.val).re := by
  simpa only [pow_succ (-1:ℝ),hodd.neg_one_pow,neg_mul_neg,one_mul] using
    sourceSection26_action_estimate m hm a

end NLS.ZakharovShabat
