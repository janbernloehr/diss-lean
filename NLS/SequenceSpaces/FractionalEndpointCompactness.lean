import NLS.SequenceSpaces.FractionalBandDecay

/-! A bounded fractional operator compatible with the rough endpoint
and an L2 one-smoothing operator is compact for every strict fractional order. -/
noncomputable section
open Filter
namespace NLS.WeightedCoeff

theorem isCompactOperator_fractional_of_endpoint_bounds
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (B₀ : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ]
      WeightedCoeff (Weight.signedSobolev (-1/2)) 2)
    (B₁ : WeightedCoeff (Weight.sobolev 0) 2 →L[ℂ]
      WeightedCoeff (Weight.signedSobolev (3/2)) 2)
    (B : WeightedCoeff (Weight.sobolev (-r)) 2 →L[ℂ]
      WeightedCoeff (Weight.signedSobolev (1/2-r)) 2)
    (h₀ : ∀ (N : ℕ) (a : WeightedCoeff (Weight.sobolev (-r)) 2) (k : ℤ),
      (B₀ (frequencyBand (Weight.sobolev (-1)) N a.val)).val k =
        (B (frequencyBand (Weight.sobolev (-r)) N a.val)).val k)
    (h₁ : ∀ (N : ℕ) (a : WeightedCoeff (Weight.sobolev (-r)) 2) (k : ℤ),
      (B₁ (frequencyBand (Weight.sobolev 0) N a.val)).val k =
        (B (frequencyBand (Weight.sobolev (-r)) N a.val)).val k) :
    IsCompactOperator B := by
  let P := fun j : ℕ => frequencyProjection (Weight.sobolev (-r)) (2^j)
  let C := (‖B₀‖+‖B₁‖+1)*(2:ℝ)^r
  let ρ := (2:ℝ)^(-((1-r)/2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2)
    linarith
  have hpow (j : ℕ) : (((2^j:ℕ):ℝ))^(-((1-r)/2)) = ρ^j := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
      mul_comm, Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
  have hbound (j : ℕ) : ‖B.comp (P (j+1))-B.comp (P j)‖ ≤ C*ρ^j := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (pow_nonneg hρ j))
    intro a
    have he : frequencyBand (Weight.sobolev (-r)) (2^j) a.val = P (j+1) a-P j a := by
      dsimp only [P]
      simpa only [pow_succ, mul_comm] using
        frequencyBand_eq_projection_sub (Weight.sobolev (-r)) (2^j) a
    change ‖B (P (j+1) a)-B (P j a)‖ ≤ _
    rw [← map_sub, ← he]
    have hN : 1 ≤ 2^j := Nat.one_le_pow j 2 (by norm_num)
    have hh := norm_fractional_band_le r hr hr1 B₀ B₁ B (2^j) hN a (h₀ (2^j) a) (h₁ (2^j) a)
    simpa only [hpow, C] using hh
  apply NLS.FunctionalAnalysis.isCompactOperator_of_summable_blocks B P
    (tendsto_dyadicFrequencyProjection (Weight.sobolev (-r)))
    (fun j => isCompactOperator_frequencyProjection _ _)
  exact ((summable_geometric_of_lt_one hρ hρ1).mul_left C).of_nonneg_of_le
    (fun j => norm_nonneg _) hbound

end NLS.WeightedCoeff
