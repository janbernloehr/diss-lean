import NLS.ZakharovShabat.SourceHamiltonianUnweightedRemainder
import NLS.ZakharovShabat.SourcePiSobolevCoercivity

/-! # Theorem 23.2(ii): the converse action estimate in exact physical norms -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Theorem 23.2(ii), with one constant for every real source at each integer order. -/
theorem exists_sourceSobolev_weightedAction_lower_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      ‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2 ≤ d^2*
        ((∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
          (1+∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
            (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n)) := by
  by_cases hmone : m = 1
  · subst m
    refine ⟨Real.sqrt 3, Real.sqrt_nonneg _, ?_⟩
    intro a
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    have hn := sourceH1_third_norm_sq_le_actions (realHigherSobolevToH1 1 le_rfl a)
    have hMS := sourceH1_action_mass_le_weighted (realHigherSobolevToH1 1 le_rfl a)
    rw [sourceH1RealSource_realHigherSobolevToH1] at hn hMS
    change (1/3:ℝ)*‖sourcePhysicalH1Coordinates (higherSobolevToH1 1 le_rfl a.val)‖^2 ≤ _ at hn
    rw [sourcePhysicalH1Coordinates_higherSobolevToH1] at hn
    have hM : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩ 0 n := by
      apply tsum_nonneg
      intro n
      unfold sourceWeightedActionTerm
      positivity
    have hb := mul_le_mul_of_nonneg_right hMS hM
    norm_num only [show 4*1-3=1 from rfl,pow_one]
    nlinarith
  have hm2 : 2 ≤ m := by omega
  obtain ⟨C,hC,hcoer⟩ := exists_sobolevOddHamiltonian_coercivity m hm
  obtain ⟨H,hH,hham⟩ := exists_sobolevOddHamiltonian_unweighted_action_bound m hm2
  let L : ℝ := 2*(2*Real.pi)^(2*m)*2^(2*m)
  let D : ℝ := L*(1+2*H+2*C)
  have hL : 0 ≤ L := by positivity
  have hD : 0 ≤ D := by positivity
  refine ⟨Real.sqrt D,Real.sqrt_nonneg _,?_⟩
  intro a
  rw [Real.sq_sqrt hD]
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  let M := ∑' n : ℤ, sourceWeightedActionTerm ψ 0 n
  let S := ∑' n : ℤ, sourceWeightedActionTerm ψ 1 n
  let T := ∑' n : ℤ, sourceWeightedActionTerm ψ m n
  let R := (1+S)^(4*m-3)*M
  let A := ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖
  let J := ‖hierarchySobolevJetL2 m m le_rfl a.val.1‖
  have hnon (k : ℕ) : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm ψ k n := by
    apply tsum_nonneg
    intro n
    unfold sourceWeightedActionTerm
    positivity
  have hM : 0 ≤ M := hnon 0
  have hS : 0 ≤ S := hnon 1
  have hT : 0 ≤ T := hnon m
  have hR : 0 ≤ R := by positivity
  have hMS : M ≤ S := by
    simpa only [sourceH1RealSource_realHigherSobolevToH1] using
      sourceH1_action_mass_le_weighted (realHigherSobolevToH1 m hm a)
  have hmass : M = A^2 := sourceHigher_sum_actions_eq_scalar_mass m hm a
  have hone : 1 ≤ (1+S)^(4*m-3) := one_le_pow₀ (by linarith)
  have hMR : M ≤ R := by
    dsimp [R]
    exact le_mul_of_one_le_left hM hone
  have hpow : M^(2*m) ≤ (1+S)^(4*m-3) :=
    (pow_le_pow_left₀ hM (by linarith : M ≤ 1+S) (2*m)).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1+S) (by omega))
  have hApow : A^(4*m) = M^(2*m) := by
    rw [hmass,← pow_mul]
    congr 1
    omega
  have herr : (1+A^(4*m))*A^2 ≤ 2*R := by
    rw [hApow,← hmass]
    have hb := mul_le_mul_of_nonneg_right (show 1+M^(2*m) ≤ 2*(1+S)^(4*m-3) by linarith) hM
    dsimp [R]
    nlinarith
  have hj : J^2 ≤ 2*H*(T+R)+2*C*R := by
    have hc := hcoer a
    have hh := hham a
    have hr := mul_le_mul_of_nonneg_left herr hC
    change J^2 ≤ 2*(sobolevOddHamiltonian m hm a.val).re+C*(1+A^(4*m))*A^2 at hc
    change (sobolevOddHamiltonian m hm a.val).re ≤ H*(T+R) at hh
    nlinarith
  have hnorm := sourcePiSobolev_norm_sq_le_mass_add_highestJet m a
  change ‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2 ≤ L*(A^2+J^2) at hnorm
  rw [← hmass] at hnorm
  change _ ≤ D*(T+R)
  apply hnorm.trans
  dsimp [D]
  rw [mul_assoc L (1+2*H+2*C) (T+R)]
  apply mul_le_mul_of_nonneg_left _ hL
  nlinarith [mul_nonneg hC hT]

end NLS.ZakharovShabat
