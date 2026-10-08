import NLS.ZakharovShabat.Lemma272ConstantBudget
import NLS.ZakharovShabat.SobolevHamiltonianThirdActionBound

/-! # The exact action-only bound of Lemma 27.2 for m ≥ 2

The endpoint m=1 is separate: the estimate below only uses it under an explicit
small-action hypothesis. No unrestricted endpoint assertion is made here.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- Lemma 27.2 with its printed constant and weighted final factor, for m ≥ 2. -/
theorem sobolevOddHamiltonian_le_weighted_actions (m : ℕ) (hm : 2 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (sobolevOddHamiltonian m (by omega) a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
      (64*Real.pi)^(2*m-2)*
        (1+∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
        (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n) := by
  have hm1 : 1 ≤ m := by omega
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  let M := ∑' n : ℤ, sourceWeightedActionTerm ψ 0 n
  let S := ∑' n : ℤ, sourceWeightedActionTerm ψ 1 n
  have hM : 0 ≤ M := by
    apply tsum_nonneg
    intro n
    unfold sourceWeightedActionTerm
    positivity
  have hMS : M ≤ S := by
    simpa only [sourceH1RealSource_realHigherSobolevToH1] using
      sourceH1_action_mass_le_weighted (realHigherSobolevToH1 m hm1 a)
  have hP : ‖sourcePiSobolevCoordinates m 1 hm1 a.val‖^2 ≤ (8/3:ℝ)*(S+M^2) := by
    have h := sourceH1_norm_sq_le_eight_thirds_actions (realHigherSobolevToH1 m hm1 a)
    rw [sourceH1RealSource_realHigherSobolevToH1] at h
    change ‖sourcePhysicalH1Coordinates (higherSobolevToH1 m hm1 a.val)‖^2 ≤ _ at h
    rwa [sourcePhysicalH1Coordinates_higherSobolevToH1] at h
  exact (sobolevOddHamiltonian_le_actions_add_H1_action_remainder m hm1 a).trans
    (add_le_add le_rfl (lemma272_central_budget m hm
      ‖sourcePiSobolevCoordinates m 1 hm1 a.val‖ M S hM hMS hP))

/-- The printed m=1 expression follows from Lemma 27.1 when the weighted action sum is ≤ 1. -/
theorem sourceH1_energy_le_lemma272_of_weighted_actions_le_one
    (a : realTypeSobolevSourceLocus)
    (hsmall : (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) ≤ 1) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      (1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) := by
  have hM : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n := by
    apply tsum_nonneg
    intro n
    unfold sourceWeightedActionTerm
    positivity
  have hMS := sourceH1_action_mass_le_weighted a
  have hS := hM.trans hMS
  have hsquare := pow_le_pow_left₀ hM hMS 2
  have hunit := mul_nonneg hS (sub_nonneg.mpr hsmall)
  nlinarith [sourceH1_energy_le_weighted_actions a]

end NLS.ZakharovShabat
