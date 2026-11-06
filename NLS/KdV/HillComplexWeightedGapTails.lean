import NLS.KdV.HillComplexWeightedGapSquares

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillNativeComplexGapSquare_weighted_tail_bound (w : SpectralWeight) (B : ℝ) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖≤B →
      ∀ N : ℕ, N0≤N → 8*‖q‖≤(N:ℝ) →
        Summable (fun k : ℕ => (w (2*((k+N:ℕ):ℤ)))^2*‖hillNativeComplexGapSquare h0q h0r w (k+N) q‖) ∧
        (∑' k : ℕ, (w (2*((k+N:ℕ):ℤ)))^2*‖hillNativeComplexGapSquare h0q h0r w (k+N) q‖) ≤
          9*‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖^2+
            2304*‖q‖^4/(N:ℝ) := by
  obtain ⟨N0,hN0,hpoint⟩ := exists_hillNativeComplexGapSquare_weighted_pointwise_bound h0q h0r w B
  refine ⟨N0,hN0,?_⟩
  intro q hq N hNN0 hcut
  have hN := hN0.trans hNN0
  let a := WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q
  let A := fun k : ℕ => ‖a ((k:ℤ)+N)‖^2+‖a (-((k:ℤ)+N))‖^2
  let R := fun k : ℕ => 1/((k:ℝ)+N)^2
  let C := 1152*‖q‖^4
  have hA : Summable A := (Coeff.positive_pair_tail_sq a N hN).1
  have hAn : (∑' k, A k)≤‖Coeff.fourierTail N a‖^2 := (Coeff.positive_pair_tail_sq a N hN).2
  have hR : Summable R := ReciprocalSeries.summable_nat_reciprocal_sq_tail N hN
  have hRn : (∑' k, R k)≤2/(N:ℝ) := ReciprocalSeries.tsum_nat_reciprocal_sq_tail_le N hN
  have hcoef (j : ℤ) : ‖a j‖^2=(w (2*j))^2*‖q.val j‖^2 := hillPeriodOne_weighted_coefficient_sq w q j
  have hmajor : Summable (fun k : ℕ => 9*A k+C*R k) := (hA.mul_left 9).add (hR.mul_left C)
  have hb (k : ℕ) :
      (w (2*((k+N:ℕ):ℤ)))^2*‖hillNativeComplexGapSquare h0q h0r w (k+N) q‖≤9*A k+C*R k := by
    have hk : N0≤k+N := by omega
    have hcutk : 8*‖q‖≤(k+N:ℕ) := hcut.trans (by exact_mod_cast (show N≤k+N by omega))
    have h := hpoint q hq (k+N) hk hcutk
    apply h.trans_eq
    dsimp only [A,R,C]
    rw [hcoef,hcoef,mul_neg,w.apply_neg]
    push_cast
    ring
  have hs := Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (norm_nonneg _)) hb hmajor
  refine ⟨hs,?_⟩
  calc
    _ ≤ ∑' k : ℕ, (9*A k+C*R k) := hs.tsum_le_tsum hb hmajor
    _ = 9*(∑' k : ℕ, A k)+C*(∑' k : ℕ, R k) := by
      rw [(hA.mul_left 9).tsum_add (hR.mul_left C),tsum_mul_left,tsum_mul_left]
    _ ≤ 9*‖Coeff.fourierTail N a‖^2+C*(2/(N:ℝ)) := by gcongr
    _ = _ := by dsimp only [C,a];ring

theorem exists_hillNativeComplexGapSquare_weighted_uniform_bound (w : SpectralWeight) (B : ℝ) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ N : ℕ, N0≤N → ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖≤B →
      Summable (fun k : ℕ => (w (2*((k+N:ℕ):ℤ)))^2*‖hillNativeComplexGapSquare h0q h0r w (k+N) q‖) ∧
      (∑' k : ℕ, (w (2*((k+N:ℕ):ℤ)))^2*‖hillNativeComplexGapSquare h0q h0r w (k+N) q‖)≤9*B^2+2304*B^4 := by
  obtain ⟨Np,hNp,htail⟩ := exists_hillNativeComplexGapSquare_weighted_tail_bound h0q h0r w B
  obtain ⟨M,hM⟩ := exists_nat_ge (8*B)
  refine ⟨Np+M,hNp.trans (by omega),?_⟩
  intro N hN q hq
  have hcut : 8*‖q‖≤(N:ℝ) :=
    (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤8)).trans (hM.trans (by exact_mod_cast (show M≤N by omega)))
  obtain ⟨hs,hb⟩ := htail q hq N (by omega) hcut
  refine ⟨hs,?_⟩
  have hNr : (1:ℝ)≤N := by exact_mod_cast (hNp.trans (show Np≤N by omega))
  have ht := Coeff.norm_fourierTail_le (by norm_num : (2:ℝ≥0∞)≠0) N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)
  rw [← WeightedCoeff.norm_eq] at ht
  have hts : ‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖^2≤‖q‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hq2 : ‖q‖^2≤B^2 := pow_le_pow_left₀ (norm_nonneg q) hq 2
  have hq4 : ‖q‖^4≤B^4 := pow_le_pow_left₀ (norm_nonneg q) hq 4
  have hrem : 2304*‖q‖^4/(N:ℝ)≤2304*‖q‖^4 := div_le_self (by positivity) hNr
  exact hb.trans (by nlinarith)

end NLS.KdV
