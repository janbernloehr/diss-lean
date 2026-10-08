import NLS.ZakharovShabat.SourceWeightedActionMajorant
import NLS.ZakharovShabat.SobolevOddHamiltonianReal

/-! # The summed action estimate, with the trace-consistent Hamiltonian sign

With the Hamiltonians defined in Appendix H and trace (5.4), the last term
is +2^m H_(2m+1). The extra (-1)^(m+1) printed in Lemma 26.2 conflicts with
that trace at even m. We retain the physical Hamiltonian definition and
state the positive-sign estimate explicitly, rather than silently changing
normalization. The stronger mass coefficient one half is also retained.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- Odd real higher actions are absolutely summable on the sharp H^m space. -/
theorem sourceRealHigherActions_summable (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    Summable (fun n : ℤ => sourceRealHigherAction (by simp) (by norm_num)
      ⟨higherSobolevSourceInclusion m a.val,a.property⟩ n (2*m)) := by
  obtain ⟨U,_,ha,h⟩ := exists_local_sobolevOddHamiltonian_trace m hm a
  have hs := (h a.val ha).2
  have hs' : Summable (fun n : ℤ => ‖sourceRealHigherAction (by simp) (by norm_num)
      ⟨higherSobolevSourceInclusion m a.val,a.property⟩ n (2*m)‖) := by
    simpa only [sourceComplexHigherAction_eq_real (φ :=
      (⟨higherSobolevSourceInclusion m a.val,a.property⟩ : realTypeSourceSubmodule 2)),Complex.norm_real] using hs
  exact hs'.of_norm

/-- The trace term used to sum Proposition 26.1 has a positive sign at every order. -/
theorem eight_pow_mul_tsum_realHigherActions (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    8^m*(∑' n : ℤ, sourceRealHigherAction (by simp) (by norm_num)
      ⟨higherSobolevSourceInclusion m a.val,a.property⟩ n (2*m)) =
      2^m*(sobolevOddHamiltonian m hm a.val).re := by
  rw [sobolevOddHamiltonian_eq_real_action_sum,Complex.ofReal_re,← mul_assoc,← mul_pow]
  norm_num

/-- The trace-consistent form of Lemma 26.2, strengthened by the exact half-mass factor. -/
theorem sourceWeightedAction_summable_and_le_half_mass (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ =
      periodOnePotential (higherSobolevSourceInclusion m a.val)) :
    Summable (sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m) ∧
    (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n) ≤
      (1+16*Real.pi)^(2*m)*(1+‖φ‖)^(4*m)*(‖higherSobolevSourceInclusion m a.val‖^2/2)+
      2^m*(sobolevOddHamiltonian m hm a.val).re := by
  have h := sourceWeightedAction_summable_and_le_higher_sum
    ⟨higherSobolevSourceInclusion m a.val,a.property⟩ φ hφ m
    (sourceRealHigherActions_summable m hm a)
  rwa [eight_pow_mul_tsum_realHigherActions m hm a] at h

/-- The source remainder constant with the Hamiltonian sign required by (5.4). -/
theorem sourceWeightedAction_le_mass (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ =
      periodOnePotential (higherSobolevSourceInclusion m a.val)) :
    (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n) ≤
      (1+16*Real.pi)^(2*m)*(1+‖φ‖)^(4*m)*‖higherSobolevSourceInclusion m a.val‖^2+
      2^m*(sobolevOddHamiltonian m hm a.val).re := by
  apply (sourceWeightedAction_summable_and_le_half_mass m hm a φ hφ).2.trans
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖higherSobolevSourceInclusion m a.val‖]) (by positivity)

/-- At even m the printed signed trace equality holds only when the Hamiltonian vanishes. -/
theorem printed_even_trace_identity_iff_zero (m : ℕ) (hm : 1 ≤ m) (heven : Even m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (8^m*(∑' n : ℤ, sourceRealHigherAction (by simp) (by norm_num)
      ⟨higherSobolevSourceInclusion m a.val,a.property⟩ n (2*m)) =
      (-1:ℝ)^(m+1)*2^m*(sobolevOddHamiltonian m hm a.val).re) ↔
      (sobolevOddHamiltonian m hm a.val).re = 0 := by
  rw [eight_pow_mul_tsum_realHigherActions m hm a, pow_succ (-1 : ℝ), heven.neg_one_pow]
  have h2 : (0:ℝ) < 2^m := by positivity
  constructor <;> intro h <;> nlinarith

end NLS.ZakharovShabat
