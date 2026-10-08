import NLS.ZakharovShabat.M1ExteriorGapBudget
import NLS.SequenceSpaces.SpectralWeightInterpolation

/-! # Scalar and mass budgets for the real weighted action estimate -/
noncomputable section
namespace NLS.ZakharovShabat

/-- The source's unweighted Hilbert norm is bounded by any exact weighted realization. -/
theorem source_norm_sq_le_weighted_realization (w : SpectralWeight) (ψ : CoeffPair 2)
    (φ : WeightedCoeffPair w.toWeight 2) (hφ : weightedBaseToPair w φ = periodOnePotential ψ) :
    ‖ψ‖^2 ≤ ‖φ‖^2 := by
  have hf := congrArg Prod.fst hφ
  have hg := congrArg Prod.snd hφ
  change SpectralWeight.toCoeff w φ.fst = Coeff.periodDouble ψ.fst at hf
  change SpectralWeight.toCoeff w φ.snd = Coeff.periodDouble ψ.snd at hg
  have hfn := SpectralWeight.norm_toCoeff_le w φ.fst
  have hgn := SpectralWeight.norm_toCoeff_le w φ.snd
  rw [hf,Coeff.norm_periodDouble] at hfn
  rw [hg,Coeff.norm_periodDouble] at hgn
  rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hfn 2) (pow_le_pow_left₀ (norm_nonneg _) hgn 2)

/-- The parameter-one version of the gap-tail budget used in Section 28. -/
theorem M1_canonicalGap_tail_six_144 (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) :
    (∑' n : ℤ, if N ≤ n.natAbs then
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2 else 0) ≤
      6*‖φ‖^2+144*‖φ‖^4 := by
  have h := (M1_canonicalGap_tail_summable_and_le w hw φ heven N hN).2
  have ht := pow_le_pow_left₀ (norm_nonneg _)
    (norm_weightedPairFourierTail_le (by simp) w.toWeight (2*N) φ) 2
  have hrem : 1152/(1+(N:ℝ))*‖φ‖^6 ≤ 144*‖φ‖^4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 1+(N:ℝ))).mpr
    have hh := mul_le_mul_of_nonneg_right hN (pow_nonneg (norm_nonneg φ) 4)
    nlinarith
  linarith

/-- The interpolated M₁ weight absorbs a quadratic norm without changing its argument. -/
theorem norm_sq_le_M1_weight_at_sixteen (w : SpectralWeight) (hw : w.HasLinearFactor) (P : ℝ) :
    P^2 ≤ w.realExtension (16*P^2) := by
  let n : ℕ := ⌊16*P^2⌋₊
  have h := SpectralWeight.bracket_le_of_hasLinearFactor hw (n:ℤ)
  simp only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at h
  have he := (w.realExtension_bounds (16*P^2)).1
  simp only [abs_of_nonneg (by positivity : 0 ≤ 16*P^2)] at he
  have hn := Nat.lt_floor_add_one (16*P^2)
  change 16*P^2 < (n:ℝ)+1 at hn
  nlinarith [h.trans he,sq_nonneg P]

/-- The real-source central and tail budgets fit inside the printed constant 2²⁰. -/
theorem weighted_action_two_pow_twenty_budget (q W : ℝ) (hq : 0 ≤ q)
    (hW : 1 ≤ W) (hqW : q ≤ W) :
    W^2*q+1536*(1+q)*(6*q+144*q^2) ≤ (2:ℝ)^20*W^2*q := by
  have hsmall : 6*q+144*q^2 ≤ 144*(1+q)*q := by nlinarith
  have htail := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 1536*(1+q))
  have hsq : (1+q)^2 ≤ (2*W)^2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hmul := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ 221184*q)
  have hnonneg := mul_nonneg (sq_nonneg W) hq
  norm_num
  nlinarith

end NLS.ZakharovShabat
