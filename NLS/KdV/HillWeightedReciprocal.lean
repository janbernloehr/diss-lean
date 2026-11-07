import NLS.KdV.HillHalfDenominator

/-! Weighted reciprocal bounds for the source Hilbert-space sandwich.
All original signed Fourier modes and both source-circle resonances remain. -/
noncomputable section
open Set Metric
namespace NLS.KdV

/-- A weighted real reciprocal is controlled by the near/far free denominator
bounds throughout the full Sobolev range 0<=r<=1. -/
theorem hill_power_ratio_of_far_bound (r N K d : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hN : 1 ≤ N) (hK : 0 ≤ K) (hd : N ≤ d) (hfar : 2*N < K → K^2 ≤ 2*d) :
    (1+K)^(2*r) ≤ 16*N^(2*r-1)*d := by
  have hNp : 0 < N := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hp0 : 0 ≤ N^(2*r-1) := by positivity
  have hpow : N^(2*r-1)*N = N^(2*r) := by
    calc
      _ = N^(2*r-1)*N^(1:ℝ) := by rw [Real.rpow_one]
      _ = N^((2*r-1)+1) := (Real.rpow_add hNp _ _).symm
      _ = _ := by congr 1;ring
  have hNpow : 0 ≤ N^(2*r) := by positivity
  by_cases hn : K ≤ 2*N
  · have hb : (1+K)^(2*r) ≤ 9*N^(2*r) := by
      calc
        _ ≤ (3*N)^(2*r) := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
        _ = 3^(2*r)*N^(2*r) := Real.mul_rpow (by norm_num) hNp.le
        _ ≤ 9*N^(2*r) := mul_le_mul_of_nonneg_right
          (by have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
                (show 2*r ≤ 2 by linarith)
              exact h.trans_eq (by norm_num)) (by positivity)
    have ht := mul_le_mul_of_nonneg_left hd (show 0 ≤ 16*N^(2*r-1) by positivity)
    rw [mul_assoc, hpow] at ht
    linarith
  · have hKN : N ≤ K := by linarith
    have hKp : 0 < K := hNp.trans_le hKN
    have hK1 : 1 ≤ K := hN.trans hKN
    have hb : (1+K)^(2*r) ≤ 4*K^(2*r) := by
      calc
        _ ≤ (2*K)^(2*r) := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
        _ = 2^(2*r)*K^(2*r) := Real.mul_rpow (by norm_num) hKp.le
        _ ≤ 4*K^(2*r) := mul_le_mul_of_nonneg_right
          (by have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
                (show 2*r ≤ 2 by linarith)
              exact h.trans_eq (by norm_num)) (by positivity)
    have hkpow : K^(2*r) = K^(2*r-2)*K^2 := by
      rw [← Real.rpow_two,← Real.rpow_add hKp]
      congr 1
      ring
    have hdec : K^(2*r-2) ≤ N^(2*r-1) :=
      (Real.rpow_le_rpow_of_nonpos hNp hKN (by linarith)).trans
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
    rw [hkpow] at hb
    have hsq := hfar (by linarith)
    have h1 := mul_le_mul_of_nonneg_right hdec (sq_nonneg K)
    have h2 := mul_le_mul_of_nonneg_left hsq hp0
    nlinarith

/-- In the far Fourier region the actual original source-circle denominator
controls the full square of the signed Fourier index. -/
theorem freeHillSourceCircle_far_denominator (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) (hk : 2*(n:ℝ) < |(k:ℝ)|) :
    |(k:ℝ)|^2 ≤ 2*‖z-(freeHillValue k:ℂ)‖ := by
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hkn : k.natAbs ≠ n := by
    intro he
    have he' : |(k:ℝ)| = n := by exact_mod_cast (show |k|=(n:ℤ) by rw [← Int.natCast_natAbs,he])
    linarith
  have hd := freeHill_denominator_lower hn
    (freeHillSourceDisk_subset_strip n hn (sphere_subset_closedBall hz)) hkn
  have hg := (neg_le_abs ((n:ℝ)^2-(k:ℝ)^2)).trans hd
  nlinarith [sq_abs (k:ℝ),sq_nonneg (|(k:ℝ)|-2*(n:ℝ))]

/-- The exact source weighted reciprocal supremum has the power n^(2r-1),
including both resonant modes and every 0<=r<=1. -/
theorem freeHillSourceCircle_weighted_reciprocal_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    (Weight.sobolev r k)^2 * ‖z-(freeHillValue k:ℂ)‖⁻¹ ≤ 16*(n:ℝ)^(2*r-1) := by
  have hd := freeHillSourceCircle_denominator_ge n hn z hz k
  have hdp : 0 < ‖z-(freeHillValue k:ℂ)‖ := (by exact_mod_cast hn : (0:ℝ) < n).trans_le hd
  have hp := hill_power_ratio_of_far_bound r n |(k:ℝ)| ‖z-(freeHillValue k:ℂ)‖ hr hr1
    (by exact_mod_cast hn) (abs_nonneg _) hd (freeHillSourceCircle_far_denominator n hn z hz k)
  have hw : (Weight.sobolev r k)^2 = (1+|(k:ℝ)|)^(2*r) := by
    rw [Weight.sobolev_apply,← Real.rpow_mul_natCast (by positivity)]
    congr 1
    ring
  rw [hw,← div_eq_mul_inv]
  exact (div_le_iff₀ hdp).mpr hp

end NLS.KdV
