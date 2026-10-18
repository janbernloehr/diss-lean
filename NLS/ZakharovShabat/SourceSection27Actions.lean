import NLS.ZakharovShabat.SourceSection23Actions
import NLS.ZakharovShabat.SourceH1EndpointActionBound
import NLS.ZakharovShabat.SourceActionSobolevLowerBound

/-! # Section 27 estimates for the original indexed actions

The physical norms and Hamiltonians retain their independent definitions.
This file proves Lemma 27.2 for m≥2 and for m=1 on S≤2, and also retains
the weaker all-order bound with twice the remainder. The later module
`SourceSection27SharpEndpoint` proves the printed coefficient for every m≥1.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- Lemma 27.1 with original indexed actions and the literal signed kinetic weights. -/
theorem sourceSection27_energy_action_bound (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevHamiltonian a.val).re-2*(periodOneSobolevMass a.val).re^2 ≤
      ∑' n : ℤ, (2*Real.pi*(n:ℝ))^2*
        (sourceIndexedAction (by simp) (by norm_num) n (sourceH1RealSource a).val).re := by
  simpa only [sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) _ _
    (sourceH1RealSource a).property] using sourceH1_energy_action_bound a

/-- The exact physical pair H¹ norm, including the printed coefficient 1/3. -/
theorem sourceSection27_H1_norm (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (1/3:ℝ)*‖sourcePiSobolevCoordinates m 1 hm a.val‖^2 ≤
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)+
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n)^2 := by
  simp only [sourceIndexedWeightedActionTerm_eq]
  have h := sourceH1_third_norm_sq_le_actions (realHigherSobolevToH1 m hm a)
  rw [sourceH1RealSource_realHigherSobolevToH1] at h
  change (1/3:ℝ)*‖sourcePhysicalH1Coordinates (higherSobolevToH1 m hm a.val)‖^2 ≤ _ at h
  rwa [sourcePhysicalH1Coordinates_higherSobolevToH1] at h

/-- Lemma 27.2 with its exact printed constant at every order m≥2. -/
theorem sourceSection27_hamiltonian_estimate (m : ℕ) (hm : 2 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (sobolevOddHamiltonian m (by omega) a.val).re ≤
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
      (64*Real.pi)^(2*m-2)*
        (1+∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
        (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n) := by
  simpa only [sourceIndexedWeightedActionTerm_eq] using sobolevOddHamiltonian_le_weighted_actions m hm a

/-- The proved all-order variant with twice the printed remainder; m=1 is explicit. -/
theorem sourceSection27_hamiltonian_estimate_all (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (sobolevOddHamiltonian m hm a.val).re ≤
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
      2*(64*Real.pi)^(2*m-2)*
        (1+∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
        (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n) := by
  simpa only [sourceIndexedWeightedActionTerm_eq] using
    sobolevOddHamiltonian_le_twice_weighted_action_remainder m hm a

/-- Half the pair derivative energy is exactly the first component energy. -/
theorem sourceSection27_pair_jet_norm (m : ℕ)
    (a : realTypeHigherSobolevSourceLocus m) :
    (1/2:ℝ)*(‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2+
      ‖hierarchySobolevJetL2 m m le_rfl a.val.2‖^2) =
        ‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2 := by
  rw [hierarchySobolevJetL2_real m m le_rfl a.val.1 a.val.2
    (realTypeHigherSobolevSource_coefficients m a),norm_star,Coeff.reflection.norm_map]
  ring

/-- The sharp odd Hamiltonian agrees with the physical H¹ Hamiltonian at m=1. -/
theorem sourceSection27_H3_bridge (a : realTypeHigherSobolevSourceLocus 1) :
    (sobolevOddHamiltonian 1 le_rfl a.val).re =
      (periodOneSobolevHamiltonian (realHigherSobolevToH1 1 le_rfl a).val).re := by
  have hh := congrArg Complex.re (sobolevOddHamiltonian_eq_real_action_sum 1 le_rfl a)
  have ht := sourceH1_four_mul_sum_realThirdActions (realHigherSobolevToH1 1 le_rfl a)
  rw [sourceH1RealSource_realHigherSobolevToH1] at ht
  norm_num only [pow_one,Complex.ofReal_re] at hh
  exact hh.trans ht

/-- The literal m=1 coefficient holds on the closed weighted-action ball S≤2. -/
theorem sourceSection27_endpoint_of_small (a : realTypeHigherSobolevSourceLocus 1)
    (hsmall : (∑' n : ℤ,
      sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩ 1 n) ≤ 2) :
    (sobolevOddHamiltonian 1 le_rfl a.val).re ≤
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩ 1 n)+
      (1+∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩ 1 n)*
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩ 1 n) := by
  simp only [sourceIndexedWeightedActionTerm_eq] at hsmall ⊢
  rw [sourceSection27_H3_bridge]
  have hsmall' : (∑' n : ℤ,
      sourceWeightedActionTerm (sourceH1RealSource (realHigherSobolevToH1 1 le_rfl a)) 1 n) ≤ 2 := by
    simpa only [sourceH1RealSource_realHigherSobolevToH1] using hsmall
  simpa only [sourceH1RealSource_realHigherSobolevToH1] using
    sourceH1_energy_le_lemma272_of_weighted_actions_le_two (realHigherSobolevToH1 1 le_rfl a) hsmall'

/-- Theorem 23.2(ii) with one constant before all sources and the unweighted final action factor. -/
theorem exists_sourceSection27_sobolev_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      ‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2 ≤ d^2*
        ((∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
          (1+∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
            (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n)) := by
  simpa only [sourceIndexedWeightedActionTerm_eq] using exists_sourceSobolev_weightedAction_lower_bound m hm

/-- The H₃ corollary of Lemma 27.1 uses the original weighted and total actions. -/
theorem sourceSection27_H3_action_mass_bound (a : realTypeHigherSobolevSourceLocus 1) :
    (sobolevOddHamiltonian 1 le_rfl a.val).re ≤
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩ 1 n)+
      2*(∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩ 0 n)^2 := by
  rw [sourceSection27_H3_bridge]
  simpa only [sourceIndexedWeightedActionTerm_eq,sourceH1RealSource_realHigherSobolevToH1] using
    sourceH1_energy_le_weighted_actions (realHigherSobolevToH1 1 le_rfl a)

/-- The kinetic series in Lemma 27.1 is absolutely convergent. -/
theorem sourceSection27_kinetic_summable (a : realTypeSobolevSourceLocus) :
    Summable (fun n : ℤ => ‖(2*(Real.pi:ℂ)*n)^2*
      sourceIndexedAction (by simp) (by norm_num) n (sourceH1RealSource a).val‖) := by
  simpa only [sourceSobolevWeightedAction,sourceH1RealSource,
    sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) _ _ a.property,
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) _ _ a.property] using
      summable_norm_sourceSobolevWeightedAction a.val a.property

end NLS.ZakharovShabat
