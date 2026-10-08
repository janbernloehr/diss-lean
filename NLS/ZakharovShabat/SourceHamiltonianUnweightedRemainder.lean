import NLS.ZakharovShabat.UnweightedActionRemainderBudget
import NLS.ZakharovShabat.SobolevHamiltonianThirdActionBound

/-! # Odd Hamiltonians with an unweighted action remainder -/
noncomputable section
namespace NLS.ZakharovShabat

/-- The estimate required by Theorem 23.2(ii), with a constant uniform over H^m. -/
theorem exists_sobolevOddHamiltonian_unweighted_action_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      (sobolevOddHamiltonian m (by omega) a.val).re ≤ C*
        ((∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
          (1+∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
            (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n)) := by
  let e := 2*(m-1)
  let K : ℝ := (16*Real.pi)^e*(3*6^e)
  have hK : 0 ≤ K := by positivity
  refine ⟨1+K,by positivity,?_⟩
  intro a
  have hm1 : 1 ≤ m := by omega
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  let M := ∑' n : ℤ, sourceWeightedActionTerm ψ 0 n
  let S := ∑' n : ℤ, sourceWeightedActionTerm ψ 1 n
  let T := ∑' n : ℤ, sourceWeightedActionTerm ψ m n
  let P := ‖sourcePiSobolevCoordinates m 1 hm1 a.val‖
  have hnon (k : ℕ) : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm ψ k n := by
    apply tsum_nonneg
    intro n
    unfold sourceWeightedActionTerm
    positivity
  have hM : 0 ≤ M := hnon 0
  have hT : 0 ≤ T := hnon m
  have hS : 0 ≤ S := hnon 1
  have hMS : M ≤ S := by
    simpa only [sourceH1RealSource_realHigherSobolevToH1] using
      sourceH1_action_mass_le_weighted (realHigherSobolevToH1 m hm1 a)
  have hP : P^2 ≤ 3*(S+M^2) := by
    have h := sourceH1_third_norm_sq_le_actions (realHigherSobolevToH1 m hm1 a)
    rw [sourceH1RealSource_realHigherSobolevToH1] at h
    change (1/3:ℝ)*‖sourcePhysicalH1Coordinates (higherSobolevToH1 m hm1 a.val)‖^2 ≤ _ at h
    rw [sourcePhysicalH1Coordinates_higherSobolevToH1] at h
    dsimp [P,S,M,ψ]
    linarith
  have hinter : (1+S)^e*S ≤ T+(1+S)^(e+2)*M := by
    simpa only [show e+2 = 2*m by dsimp [e]; omega] using
      sourceWeightedAction_threshold_comparison m hm1 a (1+S) (by positivity)
  have hb := unweighted_action_remainder_budget e (by dsimp [e]; omega) P M S T hM hMS hT hP hinter
  have hb' := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (16*Real.pi)^e)
  have hham := sobolevOddHamiltonian_le_actions_add_H1_action_remainder m hm1 a
  change (sobolevOddHamiltonian m hm1 a.val).re ≤ T+(16*Real.pi)^e*(1+P^2)^e*(S+2*M^2) at hham
  change _ ≤ (1+K)*(T+(1+S)^(4*m-3)*M)
  have he : 2*e+1 = 4*m-3 := by dsimp [e]; omega
  rw [he] at hb'
  have hR : 0 ≤ (1+S)^(4*m-3)*M := by positivity
  dsimp [K] at *
  nlinarith

end NLS.ZakharovShabat
