import NLS.ZakharovShabat.SourceCentralThirdActionComparison
import NLS.ZakharovShabat.HigherSobolevH1Realization

/-! # Summing the central comparison against the physical level-three energy

This is the spectral summation step of Lemma 27.2. The remaining conversion
of the H¹ factor to the printed action-only remainder is kept separate.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- The actual odd Hamiltonian is bounded by weighted actions and the physical H¹ energy. -/
theorem sobolevOddHamiltonian_le_actions_add_H1_energy (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (sobolevOddHamiltonian m hm a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
      (16*Real.pi)^(2*(m-1))*(1+‖sourcePiSobolevCoordinates m 1 hm a.val‖^2)^(2*(m-1))*
        (periodOneSobolevHamiltonian (higherSobolevToH1 m hm a.val)).re := by
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  let φ := normalizedWeightedPeriodOne (SpectralWeight.piSobolev 1 (by norm_num))
    (sourcePiSobolevCoordinates m 1 hm a.val)
  let C : ℝ := (16*Real.pi)^(2*(m-1))*(1+‖sourcePiSobolevCoordinates m 1 hm a.val‖^2)^(2*(m-1))
  have hJ := sourceRealHigherActions_summable m hm a
  have hW := sourceWeightedAction_summable_on_Hm m hm a
  have hT : Summable (fun n : ℤ => sourceRealHigherAction (by simp) (by norm_num) ψ n 2) := by
    simpa only [sourceH1RealSource_realHigherSobolevToH1] using
      sourceH1_realThirdActions_summable (realHigherSobolevToH1 m hm a)
  have hpoint (n : ℤ) : 4^m*sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m) ≤
      sourceWeightedActionTerm ψ m n+C*(4*sourceRealHigherAction (by simp) (by norm_num) ψ n 2) := by
    simpa only [φ,C,norm_normalizedWeightedPeriodOne] using
      sourceRealHigherAction_H1_le_action_add_third ψ φ
        (weightedBaseToPair_sourcePiSobolevOne m hm a.val) n m hm
  have hsum := (hJ.mul_left ((4:ℝ)^m)).tsum_le_tsum hpoint
    (hW.add ((hT.mul_left 4).mul_left C))
  rw [tsum_mul_left, Summable.tsum_add hW ((hT.mul_left 4).mul_left C),
    tsum_mul_left, tsum_mul_left] at hsum
  have hh := congrArg Complex.re (sobolevOddHamiltonian_eq_real_action_sum m hm a)
  simp only [Complex.ofReal_re] at hh
  have ht := sourceH1_four_mul_sum_realThirdActions (realHigherSobolevToH1 m hm a)
  rw [sourceH1RealSource_realHigherSobolevToH1] at ht
  rw [← hh,ht] at hsum
  exact hsum

/-- Substituting Lemma 27.1 removes the physical energy from the central remainder. -/
theorem sobolevOddHamiltonian_le_actions_add_H1_action_remainder (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (sobolevOddHamiltonian m hm a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
      (16*Real.pi)^(2*(m-1))*(1+‖sourcePiSobolevCoordinates m 1 hm a.val‖^2)^(2*(m-1))*
        ((∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)+
          2*(∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n)^2) := by
  have h := sourceH1_energy_le_weighted_actions (realHigherSobolevToH1 m hm a)
  rw [sourceH1RealSource_realHigherSobolevToH1] at h
  apply (sobolevOddHamiltonian_le_actions_add_H1_energy m hm a).trans
  gcongr
  exact h

end NLS.ZakharovShabat
