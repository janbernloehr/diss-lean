import NLS.ZakharovShabat.SourceSobolevActionEstimate
import NLS.ZakharovShabat.SourcePiSobolevNormBounds
import NLS.ZakharovShabat.OddHamiltonianRemainderEstimate

/-! # Theorem 23.2(i): a uniform upper bound for the weighted actions

All norms use the exact physical Fourier weights and the component-sum pair
norm. The constant depends only on m; every real H^m source is admitted.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- The actual weighted action series converges at every positive integer Sobolev order. -/
theorem sourceWeightedAction_summable_on_Hm (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    Summable (sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m) := by
  exact (sourceWeightedAction_summable_and_le_half_mass m hm a
    (normalizedWeightedPeriodOne _ (sourcePiSobolevCoordinates m 1 hm a.val))
    (weightedBaseToPair_sourcePiSobolevOne m hm a.val)).1

/-- Theorem 23.2(i), with a single constant uniform over the entire real H^m space. -/
theorem exists_sourceWeightedAction_sobolev_upper_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n) ≤
        c^2*(‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2+
          (1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(4*m)*
            ‖higherSobolevSourceInclusion m a.val‖^2) := by
  obtain ⟨C,hC,hH⟩ := exists_sobolevOddHamiltonian_energy_estimates m hm 1 zero_lt_one
  let A : ℝ := 2^m*2
  let B : ℝ := (1+16*Real.pi)^(2*m)
  let D : ℝ := 2^m*C*2
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hD : 0 ≤ D := by positivity
  refine ⟨Real.sqrt (A+B+D), Real.sqrt_nonneg _, ?_⟩
  intro a
  let X := ‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2
  let R := (1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(4*m)*
    ‖higherSobolevSourceInclusion m a.val‖^2
  have hX : 0 ≤ X := by positivity
  have hR : 0 ≤ R := by positivity
  have hjet := pow_le_pow_left₀ (norm_nonneg _) (norm_highestJet_le_sourcePiSobolev m a.val) 2
  have hrem := source_scalarMass_remainder_le m hm a.val
  have hham : (sobolevOddHamiltonian m hm a.val).re ≤ 2*X+2*C*R := by
    have h := (Complex.re_le_norm _).trans (hH a).2
    have hr := mul_le_mul_of_nonneg_left hrem hC
    dsimp [X,R]
    nlinarith
  have hsum := sourceWeightedAction_le_mass m hm a
    (normalizedWeightedPeriodOne _ (sourcePiSobolevCoordinates m 1 hm a.val))
    (weightedBaseToPair_sourcePiSobolevOne m hm a.val)
  rw [norm_normalizedWeightedPeriodOne] at hsum
  have hmul := mul_le_mul_of_nonneg_left hham (by positivity : 0 ≤ (2:ℝ)^m)
  have hbound : (∑' n : ℤ, sourceWeightedActionTerm
      ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n) ≤ B*R+A*X+D*R := by
    dsimp [A,B,D,R] at *
    nlinarith
  rw [Real.sq_sqrt (by positivity : 0 ≤ A+B+D)]
  change _ ≤ (A+B+D)*(X+R)
  exact hbound.trans (by nlinarith [mul_nonneg hA hR, mul_nonneg hB hX, mul_nonneg hD hX])

end NLS.ZakharovShabat
