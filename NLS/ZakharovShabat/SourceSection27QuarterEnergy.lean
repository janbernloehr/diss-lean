import NLS.ZakharovShabat.SourceSection27Actions

/-! # The full mass remainder in the quarter-energy step of Section 27 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Retaining the full Lemma 26.3 mass remainder gives the quarter-pair-energy
bound with coefficient one on the actual Hamiltonian, uniformly on H^m. -/
theorem exists_sourceSection27_quarter_energy_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      let M := ∑' n : ℤ, sourceIndexedWeightedActionTerm
        ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n
      (1/4:ℝ)*(‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2+
        ‖hierarchySobolevJetL2 m m le_rfl a.val.2‖^2) ≤
        (sobolevOddHamiltonian m hm a.val).re+C*(1+M^(2*m))*M := by
  obtain ⟨C,hC,hbound⟩ := exists_sobolevOddHamiltonian_energy_estimates m hm (1/4) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro a
  let M := ∑' n : ℤ, sourceIndexedWeightedActionTerm
    ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n
  have hmass : M = ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^2 := by
    simp only [M,sourceIndexedWeightedActionTerm_eq]
    exact sourceHigher_sum_actions_eq_scalar_mass m hm a
  have hp : ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m) = M^(2*m) := by
    rw [hmass,← pow_mul]
    congr 1
    omega
  have hr := (abs_le.mp (hbound a).1).1
  rw [hp,← hmass] at hr
  have hj := sourceSection27_pair_jet_norm m a
  change (1/4:ℝ)*(_+_) ≤ (sobolevOddHamiltonian m hm a.val).re+C*(1+M^(2*m))*M
  nlinarith [sq_nonneg ‖hierarchySobolevJetL2 m m le_rfl a.val.1‖]

end NLS.ZakharovShabat
