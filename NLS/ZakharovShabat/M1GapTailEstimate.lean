import NLS.ZakharovShabat.M1GapTailMajorant
import NLS.ZakharovShabat.WeightedEvenLeadingTail

/-! # Proposition 25.5: the quantitative weighted gap tail

The inclusive resonance cutoff N corresponds to physical Fourier cutoff 2N.
The exact source constant 1152 follows from the pointwise constant 384 and
the bilateral reciprocal-square estimate 3/⟨N⟩.
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- Parameterized tail estimate; larger parameters reduce the nonlinear remainder. -/
theorem M1_canonicalGap_tail_summable_and_le_parameter (ε : ℝ) (hε : 0 < ε) (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2 else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2 else 0) ≤
      (3*(1+ε))*‖weightedPairFourierTail w.toWeight (2*N) φ‖^2+(576*(1+1/ε))/(1+(N:ℝ))*‖φ‖^6 := by
  let f : ℤ → ℝ := fun n => if N ≤ n.natAbs then
    (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2 else 0
  let g : ℤ → ℝ := fun n => if N ≤ n.natAbs then resonantLeadingPower w φ n else 0
  let r : ℤ → ℝ := fun n => if N ≤ n.natAbs then ReciprocalSeries.bracketInverseSq n else 0
  obtain ⟨hgs,hgb⟩ := resonantLeadingPower_tail_summable_and_le (by simp) w φ N (2*N) le_rfl
  have hrs := ReciprocalSeries.summable_bracketSquareTail N
  have hrb := ReciprocalSeries.tsum_bracketSquareTail_le N
  have hmajor : Summable (fun n => (3*(1+ε))*g n+(192*(1+1/ε))*‖φ‖^6*r n) :=
    (hgs.mul_left (3*(1+ε))).add (hrs.mul_left ((192*(1+1/ε))*‖φ‖^6))
  have hfnonneg (n : ℤ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
  have hbound (n : ℤ) : f n ≤ (3*(1+ε))*g n+(192*(1+1/ε))*‖φ‖^6*r n := by
    by_cases hn : N ≤ n.natAbs
    · have hcast : (N:ℝ) ≤ |(n:ℝ)| := by
        have h : (N:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hn
        simpa only [Nat.cast_natAbs,Int.cast_abs] using h
      simpa only [f,g,r,if_pos hn] using
        M1_canonicalGap_tail_majorant_parameter ε hε w hw φ heven n (by linarith)
    · simp only [f,g,r,if_neg hn,mul_zero,add_zero,le_refl]
  have hfs : Summable f := hmajor.of_nonneg_of_le hfnonneg hbound
  refine ⟨hfs,?_⟩
  change (∑' n, f n) ≤ _
  calc
    _ ≤ ∑' n, ((3*(1+ε))*g n+(192*(1+1/ε))*‖φ‖^6*r n) := hfs.tsum_le_tsum hbound hmajor
    _ = (3*(1+ε))*(∑' n, g n)+(192*(1+1/ε))*‖φ‖^6*(∑' n, r n) := by
      rw [Summable.tsum_add (hgs.mul_left (3*(1+ε))) (hrs.mul_left ((192*(1+1/ε))*‖φ‖^6)),tsum_mul_left,tsum_mul_left]
    _ ≤ (3*(1+ε))*‖weightedPairFourierTail w.toWeight (2*N) φ‖^2+(192*(1+1/ε))*‖φ‖^6*(3/(1+(N:ℝ))) := by
      have hg' : (∑' n, g n) ≤ ‖weightedPairFourierTail w.toWeight (2*N) φ‖^2 := by
        simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hgb
      exact add_le_add (mul_le_mul_of_nonneg_left hg' (by positivity))
        (mul_le_mul_of_nonneg_left hrb (by positivity))
    _ = _ := by ring

/-- Proposition 25.5's first estimate, with summability and the physical signed Fourier tail. -/
theorem M1_canonicalGap_tail_summable_and_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2 else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2 else 0) ≤
      6*‖weightedPairFourierTail w.toWeight (2*N) φ‖^2+1152/(1+(N:ℝ))*‖φ‖^6 := by
  convert M1_canonicalGap_tail_summable_and_le_parameter 1 (by norm_num) w hw φ heven N hN using 1
  norm_num

/-- Proposition 25.5 in the source's signed resonance-tail normalization. -/
theorem M1_canonicalGap_tail_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) :
    (∑' n : ℤ, if N ≤ n.natAbs then
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2 else 0) ≤
      6*‖weightedResonantLeadingTail w φ N‖^2+1152/(1+(N:ℝ))*‖φ‖^6 := by
  have he : ∀ k : ℤ, φ.fst.val (2*k+1) = 0 ∧ φ.snd.val (2*k+1) = 0 := by
    intro k
    have hf := (Coeff.mem_paritySubspace 0 _).mp heven.1 (2*k+1) (by omega)
    have hg := (Coeff.mem_paritySubspace 0 _).mp heven.2 (2*k+1) (by omega)
    simpa only [weightedBaseToPair_fst,weightedBaseToPair_snd] using And.intro hf hg
  rw [norm_weightedResonantLeadingTail_eq_of_even (by simp) w φ he N]
  exact (M1_canonicalGap_tail_summable_and_le w hw φ heven N hN).2

end NLS.ZakharovShabat
