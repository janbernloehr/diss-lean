import NLS.ZakharovShabat.SourceM1GapFactorBound
import NLS.ZakharovShabat.M1WeightedActionBudget
import NLS.ZakharovShabat.SourceWeightedActionMajorant
import NLS.ZakharovShabat.M1RealGlobalGapEstimate
import NLS.ZakharovShabat.NormalizedWeightedSource

/-! # Theorem 23.4: the global weighted action bound on real sources

The weight is an arbitrary member of M₁, evaluated at the exact doubled
frequency and interpolated argument 16 P² from the source. The theorem
includes absolute summability, not merely a formal bound for a total sum.
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- The literal summand of the action norm for a general spectral weight. -/
def sourceM1ActionTerm (w : SpectralWeight) (ψ : CoeffPair 2) (n : ℤ) : ℝ :=
  (w (2*n))^2*‖sourceComplexAction (by simp) (by norm_num) n ψ‖

/-- The exterior weighted action series has the quantitative gap-tail majorant. -/
theorem sourceM1_real_action_tail_summable_and_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (ψ : realTypeSourceSubmodule 2) (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ.val)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (hcut : (N:ℝ) ≤ 8*‖φ‖^2) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then sourceM1ActionTerm w ψ.val n else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then sourceM1ActionTerm w ψ.val n else 0) ≤
      1536*(1+‖φ‖^2)*(6*‖φ‖^2+144*‖φ‖^4) := by
  have heven : weightedBaseToPair w φ ∈ pairParitySubspace 0 := hφ ▸ periodOnePotential_mem ψ.val
  have hgs := (M1_canonicalGap_tail_summable_and_le w hw φ heven N hN).1
  have hgb := M1_canonicalGap_tail_six_144 w hw φ heven N hN
  simp only [hφ] at hgs hgb
  let f : ℤ → ℝ := fun n => if N ≤ n.natAbs then sourceM1ActionTerm w ψ.val n else 0
  let g : ℤ → ℝ := fun n => if N ≤ n.natAbs then
    (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n‖)^2 else 0
  let C := 1536*(1+‖φ‖^2)
  have hf0 (n : ℤ) : 0 ≤ f n := by dsimp [f,sourceM1ActionTerm]; split_ifs <;> positivity
  have hmajor (n : ℤ) : f n ≤ C*g n := by
    by_cases hn : N ≤ n.natAbs
    · have h := sourceM1_real_action_le_1536_at_cutoff w hw ψ φ hφ N hN hcut n hn
      rw [sourcePeriodicGapDisplacement_apply] at h
      have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (w (2*n)))
      simp only [f,g,C,sourceM1ActionTerm,if_pos hn]
      calc
        _ ≤ (w (2*n))^2 * (1536*(1+‖φ‖^2) *
            ‖canonicalPeriodicGap (by simp) (by norm_num)
              (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n‖^2) := hh
        _ = _ := by ring
    · simp only [f,g,if_neg hn,mul_zero,le_refl]
  have hmajors : Summable (fun n => C*g n) := hgs.mul_left C
  have hfs : Summable f := hmajors.of_nonneg_of_le hf0 hmajor
  refine ⟨hfs,?_⟩
  change (∑' n, f n) ≤ _
  calc
    _ ≤ ∑' n, C*g n := hfs.tsum_le_tsum hmajor hmajors
    _ = C*(∑' n, g n) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hgb (by dsimp [C]; positivity)

/-- The remaining central actions are controlled by the exact mass trace. -/
theorem sourceM1_real_central_actions_le (w : SpectralWeight)
    (ψ : realTypeSourceSubmodule 2) (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ.val)
    (N : ℕ) (hcut : (N:ℝ) ≤ 8*‖φ‖^2) :
    (∑ n ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), sourceM1ActionTerm w ψ.val n) ≤
      (w.realExtension (16*‖φ‖^2))^2*‖φ‖^2 := by
  let W := w.realExtension (16*‖φ‖^2)
  have he (n : ℤ) : ‖sourceComplexAction (by simp) (by norm_num) n ψ.val‖ =
      (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re := by
    rw [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n ψ.val ψ.property]
    exact norm_sourceRealAction ψ n
  have hs := (sourceRealActions_summable ψ).congr (fun n => (he n).symm)
  have ht : (∑' n : ℤ, ‖sourceComplexAction (by simp) (by norm_num) n ψ.val‖) = ‖ψ.val‖^2/2 :=
    (tsum_congr he).trans (sourceHilbert_sum_actions_eq_half_norm_sq ψ)
  have hsum := hs.sum_le_tsum (Finset.Ioo (-(N:ℤ)) (N:ℤ)) (fun n _ => norm_nonneg _)
  rw [ht] at hsum
  have hnorm := source_norm_sq_le_weighted_realization w ψ.val φ hφ
  calc
    _ ≤ ∑ n ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), W^2*‖sourceComplexAction (by simp) (by norm_num) n ψ.val‖ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnabs : n.natAbs ≤ N := by simp only [Finset.mem_Ioo] at hn; omega
      have hnR : |(n:ℝ)| ≤ (N:ℝ) := by
        have h : (n.natAbs:ℝ) ≤ (N:ℝ) := by exact_mod_cast hnabs
        simpa only [Nat.cast_natAbs,Int.cast_abs] using h
      have hwgt : w (2*n) ≤ W := w.le_realExtension _ _ (by
        simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
        linarith)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (w.positive _).le hwgt 2) (norm_nonneg _)
    _ = W^2*(∑ n ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), ‖sourceComplexAction (by simp) (by norm_num) n ψ.val‖) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖φ‖]) (sq_nonneg W)

/-- The real-source estimate in Theorem 23.4 with the printed constant 2²⁰,
including summability, every M₁ weight, and the zero source. -/
theorem sourceM1_real_weighted_actions_summable_and_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (ψ : realTypeSourceSubmodule 2) (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ.val) :
    Summable (sourceM1ActionTerm w ψ.val) ∧
    (∑' n : ℤ, sourceM1ActionTerm w ψ.val n) ≤
      (2:ℝ)^20*(w.realExtension (16*‖φ‖^2))^2*‖φ‖^2 := by
  let N : ℕ := ⌊8*‖φ‖^2⌋₊
  have hcut : (N:ℝ) ≤ 8*‖φ‖^2 := Nat.floor_le (by positivity)
  have hN : 8*‖φ‖^2 ≤ 1+(N:ℝ) := by
    have h := Nat.lt_floor_add_one (8*‖φ‖^2)
    dsimp [N]
    linarith
  obtain ⟨hts,htb⟩ := sourceM1_real_action_tail_summable_and_le w hw ψ φ hφ N hN hcut
  obtain ⟨hs,he⟩ := sum_eq_central_add_tail (sourceM1ActionTerm w ψ.val) N hts
  refine ⟨hs,?_⟩
  rw [he]
  have hc := sourceM1_real_central_actions_le w ψ φ hφ N hcut
  have hb := weighted_action_two_pow_twenty_budget (‖φ‖^2) (w.realExtension (16*‖φ‖^2))
    (sq_nonneg _) (w.one_le_realExtension _) (norm_sq_le_M1_weight_at_sixteen w hw ‖φ‖)
  have hp : (‖φ‖^2)^2 = ‖φ‖^4 := by ring
  rw [hp] at hb
  exact (add_le_add hc htb).trans hb

/-- The real weighted theorem in normalized source coordinates, with no
auxiliary realization hypothesis: their norm is exactly the physical weighted norm. -/
theorem sourceM1_real_weighted_actions_normalized (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : realTypeSourceSubmodule 2) :
    Summable (sourceM1ActionTerm w (normalizedWeightedSource w a.val)) ∧
    (∑' n : ℤ, sourceM1ActionTerm w (normalizedWeightedSource w a.val) n) ≤
      (2:ℝ)^20*(w.realExtension (16*‖a.val‖^2))^2*‖a.val‖^2 := by
  have h := sourceM1_real_weighted_actions_summable_and_le w hw
    ⟨normalizedWeightedSource w a.val,normalizedWeightedSource_realType w a.val a.property⟩
    (normalizedWeightedPeriodOne w a.val) (weightedBaseToPair_normalizedWeightedPeriodOne w a.val)
  simpa only [norm_normalizedWeightedPeriodOne] using h

end NLS.ZakharovShabat
