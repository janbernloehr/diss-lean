import NLS.ZakharovShabat.SobolevSourceFourierModes
import NLS.ZakharovShabat.OddHamiltonianRemainderEstimate
import NLS.ZakharovShabat.SourceSection23Actions

/-! # A counterexample to the full printed Lemma 26.2

Real modes with amplitude 1/n have bounded H¹ norm and growing H₅.
At m=2 the printed right-hand side becomes negative, whereas the actual
original indexed-action sum is nonnegative and absolutely convergent.
The exact physical H¹ weight also refutes the coefficient-one norm
splitting used at the end of the printed Lemma 26.3 proof.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- The high-frequency family has bounded mass and H¹ norm, and an unbounded top jet. -/
theorem section26_highMode_bounds (n : ℕ) (hn : 1 ≤ n) :
    let a := sobolevSourceRealMode 2 n (1/(n:ℝ))
    ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a.val.1‖ ≤ 1 ∧
    ‖higherSobolevSourceInclusion 2 a.val‖^2 ≤ 2 ∧
    ‖sourcePiSobolevCoordinates 2 1 (by omega) a.val‖ ≤ 2*(1+2*Real.pi) ∧
    (n:ℝ) ≤ ‖hierarchySobolevJetL2 2 2 le_rfl a.val.1‖ := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hi : |1/(n:ℝ)| ≤ 1 := by
    rw [abs_of_pos (one_div_pos.mpr hn0)]
    exact (div_le_one hn0).mpr hn'
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · change ‖WeightedCoeff.sobolevToL2 _ (sobolevSourceScalarMode 2 n (1/(n:ℝ)))‖ ≤ _
    rw [norm_sobolevSourceScalarMode_L2]
    exact hi
  · rw [sobolevSourceRealMode_mass]
    nlinarith [sq_abs (1/(n:ℝ)), abs_nonneg (1/(n:ℝ))]
  · have he := sobolevSourceRealMode_piNorm 2 1 (by omega) n (1/(n:ℝ))
    simp only [pow_one, Int.cast_natCast, abs_of_nonneg hn0.le,
      abs_of_pos (one_div_pos.mpr hn0)] at he
    have hx : (1+2*Real.pi*(n:ℝ))*(1/(n:ℝ)) ≤ 1+2*Real.pi := by
      rw [mul_one_div, div_le_iff₀ hn0]
      nlinarith
    have hx0 : 0 ≤ (1+2*Real.pi*(n:ℝ))*(1/(n:ℝ)) := by positivity
    have hp := pow_le_pow_left₀ hx0 hx 2
    have hpos : 0 < 1+2*Real.pi := by positivity
    nlinarith [norm_nonneg (sourcePiSobolevCoordinates 2 1 (by omega)
      (sobolevSourceRealMode 2 n (1/(n:ℝ))).val)]
  · change (n:ℝ) ≤ ‖hierarchySobolevJetL2 2 2 le_rfl (sobolevSourceScalarMode 2 n (1/(n:ℝ)))‖
    rw [norm_sobolevSourceScalarMode_jet]
    simp only [Int.cast_natCast, abs_of_nonneg hn0.le,
      abs_of_pos (one_div_pos.mpr hn0)]
    have he : (2*Real.pi)^2*(n:ℝ)^2*(1/(n:ℝ)) = (2*Real.pi)^2*n := by
      field_simp
    rw [he]
    have hp : (1:ℝ) ≤ (2*Real.pi)^2 := by nlinarith [Real.pi_gt_three]
    nlinarith

/-- An actual real H² source makes the full printed right-hand side negative. -/
theorem section26_printedRhs_negative :
    ∃ a : realTypeHigherSobolevSourceLocus 2,
      (1+16*Real.pi)^4*(1+‖sourcePiSobolevCoordinates 2 1 (by omega) a.val‖)^8*
        ‖higherSobolevSourceInclusion 2 a.val‖^2 - 4*(sobolevOddHamiltonian 2 (by omega) a.val).re < 0 := by
  obtain ⟨C,hC,hcoercive⟩ := exists_sobolevOddHamiltonian_coercivity 2 (by omega)
  let R : ℝ := 2*(1+16*Real.pi)^4*(1+2*(1+2*Real.pi))^8
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨n,hn⟩ := exists_nat_gt (R+4*C+1)
  have hn1 : (1:ℝ) < n := by linarith
  have hnNat : 1 ≤ n := by exact_mod_cast (le_of_lt hn1)
  let a := sobolevSourceRealMode 2 n (1/(n:ℝ))
  obtain ⟨hA,hM,hP,hJ⟩ := section26_highMode_bounds n hnNat
  change ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a.val.1‖ ≤ 1 at hA
  change ‖higherSobolevSourceInclusion 2 a.val‖^2 ≤ 2 at hM
  change ‖sourcePiSobolevCoordinates 2 1 (by omega) a.val‖ ≤ 2*(1+2*Real.pi) at hP
  change (n:ℝ) ≤ ‖hierarchySobolevJetL2 2 2 le_rfl a.val.1‖ at hJ
  have hc := hcoercive a
  have herror : C*(1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a.val.1‖^8)*
      ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a.val.1‖^2 ≤ 2*C := by
    calc
      _ ≤ C*(1+1^8)*1^2 := by gcongr
      _ = _ := by ring
  norm_num only [show 4*2 = 8 by omega] at hc
  have hjsq := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ n) hJ 2
  have hrem : (1+16*Real.pi)^4*(1+‖sourcePiSobolevCoordinates 2 1 (by omega) a.val‖)^8*
      ‖higherSobolevSourceInclusion 2 a.val‖^2 ≤ R := by
    calc
      _ ≤ (1+16*Real.pi)^4*(1+2*(1+2*Real.pi))^8*2 := by gcongr
      _ = R := by dsimp [R]; ring
  refine ⟨a,?_⟩
  nlinarith

/-- The alternating-sign inequality itself fails at m=2, including its positive remainder. -/
theorem section26_printedInequality_counterexample :
    ∃ a : realTypeHigherSobolevSourceLocus 2,
      ¬ (∑' n : ℤ, sourceIndexedWeightedActionTerm
          ⟨higherSobolevSourceInclusion 2 a.val,a.property⟩ 2 n) ≤
        (1+16*Real.pi)^4*(1+‖sourcePiSobolevCoordinates 2 1 (by omega) a.val‖)^8*
          ‖higherSobolevSourceInclusion 2 a.val‖^2 +
          (-1:ℝ)^3*2^2*(sobolevOddHamiltonian 2 (by omega) a.val).re := by
  obtain ⟨a,ha⟩ := section26_printedRhs_negative
  refine ⟨a,?_⟩
  have hs : 0 ≤ ∑' n : ℤ, sourceIndexedWeightedActionTerm
      ⟨higherSobolevSourceInclusion 2 a.val,a.property⟩ 2 n :=
    tsum_nonneg (fun n => by unfold sourceIndexedWeightedActionTerm; positivity)
  norm_num
  linarith

/-- The counterexample has an absolutely convergent original action sum and a strict reverse inequality. -/
theorem section26_printedInequality_strict_counterexample :
    ∃ a : realTypeHigherSobolevSourceLocus 2,
      Summable (sourceIndexedWeightedActionTerm
        ⟨higherSobolevSourceInclusion 2 a.val,a.property⟩ 2) ∧
      (1+16*Real.pi)^4*(1+‖sourcePiSobolevCoordinates 2 1 (by omega) a.val‖)^8*
          ‖higherSobolevSourceInclusion 2 a.val‖^2 +
          (-1:ℝ)^3*2^2*(sobolevOddHamiltonian 2 (by omega) a.val).re <
        (∑' n : ℤ, sourceIndexedWeightedActionTerm
          ⟨higherSobolevSourceInclusion 2 a.val,a.property⟩ 2 n) := by
  obtain ⟨a,ha⟩ := section26_printedInequality_counterexample
  have he (ψ : realTypeSourceSubmodule 2) : sourceIndexedWeightedActionTerm ψ 2 =
      sourceWeightedActionTerm ψ 2 := funext (sourceIndexedWeightedActionTerm_eq ψ 2)
  refine ⟨a,?_,lt_of_not_ge ha⟩
  rw [he]
  exact (sourceWeightedAction_summable_and_le_half_mass 2 (by omega) a
    (normalizedWeightedPeriodOne _ (sourcePiSobolevCoordinates 2 1 (by omega) a.val))
    (weightedBaseToPair_sourcePiSobolevOne 2 (by omega) a.val)).1

/-- With the exact physical weight, the H¹ norm splitting at the end of the printed proof is false. -/
theorem section26_printed_physicalNorm_split_counterexample :
    ∃ a : ScalarSobolev 1,
      ‖hierarchySobolevJetL2 1 1 le_rfl a‖^2+
        ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 1) a‖^2 <
          ‖sourcePiSobolevScalar 1 1 le_rfl a‖^2 := by
  refine ⟨sobolevSourceScalarMode 1 1 1,?_⟩
  rw [norm_sobolevSourceScalarMode_jet,norm_sobolevSourceScalarMode_L2,
    norm_sobolevSourceScalarMode_piCoordinates]
  norm_num
  nlinarith [Real.pi_pos]

end NLS.ZakharovShabat
