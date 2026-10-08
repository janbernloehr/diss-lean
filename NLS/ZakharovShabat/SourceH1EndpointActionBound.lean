import NLS.ZakharovShabat.Lemma272EndpointArithmetic
import NLS.ZakharovShabat.SourceHamiltonianActionOnlyBound

/-! # Stronger endpoint estimates and a uniform variant of Lemma 27.2

Retaining the mass subtraction extends the printed m=1 estimate to S ≤ 2.
The unrestricted variant below has an explicitly enlarged remainder.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- Keep the mass subtraction in the comparison with the kinetic action sum. -/
theorem sourceH1_energy_le_weighted_actions_sub_mass (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)-
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)+
      2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)^2 := by
  rw [sourceH1_sum_actions_eq_mass]
  linarith [sourceH1_energy_le_kinetic_actions a, sourceH1_kinetic_actions_add_mass_le a]

/-- The strongest mass-independent consequence of the preceding scalar budget. -/
theorem sourceH1_energy_le_max_weighted_actions (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevHamiltonian a.val).re ≤ max
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)
      (2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)^2) := by
  apply (sourceH1_energy_le_weighted_actions_sub_mass a).trans
  apply lemma272_mass_budget_le_max _ _ _ (sourceH1_action_mass_le_weighted a)
  apply tsum_nonneg
  intro n
  unfold sourceWeightedActionTerm
  positivity

/-- A mass-sensitive sufficient condition also applies outside the ball S ≤ 2. -/
theorem sourceH1_energy_le_lemma272_of_mass_budget (a : realTypeSobolevSourceLocus)
    (h : 2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)^2-
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n) ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)^2) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      (1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) := by
  nlinarith [sourceH1_energy_le_weighted_actions_sub_mass a]

/-- The literal endpoint estimate on the larger closed action ball S ≤ 2. -/
theorem sourceH1_energy_le_lemma272_of_weighted_actions_le_two
    (a : realTypeSobolevSourceLocus)
    (hsmall : (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) ≤ 2) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      (1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) := by
  have h := sourceH1_energy_le_max_weighted_actions a
  have hS : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n := by
    apply tsum_nonneg
    intro n
    unfold sourceWeightedActionTerm
    positivity
  have hb : max (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)
      (2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)^2) ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      (1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) := by
    apply max_le <;> nlinarith
  exact h.trans hb

/-- Without any smallness hypothesis, a factor two in the remainder suffices. -/
theorem sourceH1_energy_le_twice_lemma272_remainder (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      2*(1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) := by
  have h := sourceH1_energy_le_max_weighted_actions a
  have hS : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n := by
    apply tsum_nonneg
    intro n
    unfold sourceWeightedActionTerm
    positivity
  apply h.trans
  apply max_le <;> nlinarith

/-- An all-order variant, explicitly distinguished from the printed coefficient at m=1. -/
theorem sobolevOddHamiltonian_le_twice_weighted_action_remainder (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (sobolevOddHamiltonian m hm a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
      2*(64*Real.pi)^(2*m-2)*
        (1+∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
        (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n) := by
  have hS : 0 ≤ ∑' n : ℤ,
      sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n := by
    apply tsum_nonneg
    intro n
    unfold sourceWeightedActionTerm
    positivity
  by_cases hm2 : 2 ≤ m
  · apply (sobolevOddHamiltonian_le_weighted_actions m hm2 a).trans
    have hp : 0 ≤ (64*Real.pi)^(2*m-2)*
        (1+∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
        (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n) := by
      positivity
    nlinarith
  · have he : m = 1 := by omega
    subst m
    have h := sourceH1_energy_le_twice_lemma272_remainder (realHigherSobolevToH1 1 hm a)
    rw [sourceH1RealSource_realHigherSobolevToH1] at h
    have hh := congrArg Complex.re (sobolevOddHamiltonian_eq_real_action_sum 1 hm a)
    simp only [Complex.ofReal_re] at hh
    have ht := sourceH1_four_mul_sum_realThirdActions (realHigherSobolevToH1 1 hm a)
    rw [sourceH1RealSource_realHigherSobolevToH1] at ht
    norm_num only [pow_one] at hh
    rw [hh,ht]
    simpa only [show 2*1-2=0 from rfl,show 4*1-3=1 from rfl,pow_zero,pow_one,mul_one] using h

end NLS.ZakharovShabat
