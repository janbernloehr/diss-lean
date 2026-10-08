import NLS.ZakharovShabat.M1GapTailEstimate
import NLS.ZakharovShabat.M1CentralGapEstimate

/-! # The numerical budget for the global estimate in Proposition 25.5

Choosing parameter five in Young's inequality bounds the tail by
18 P² + (432/5) P⁴. This leaves enough room for a central budget
256 π² w[16 P²]² P⁴ inside the printed global constant 265 π².
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- At every valid cutoff the tail has a quartic budget compatible with the global estimate. -/
theorem M1_canonicalGap_tail_quartic_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) :
    (∑' n : ℤ, if N ≤ n.natAbs then
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2 else 0) ≤
      18*‖φ‖^2+(432/5)*‖φ‖^4 := by
  have h := (M1_canonicalGap_tail_summable_and_le_parameter 5 (by norm_num) w hw φ heven N hN).2
  norm_num at h
  have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_weightedPairFourierTail_le (by simp) w.toWeight (2*N) φ) 2
  have hrem : (3456/5)/(1+(N:ℝ))*‖φ‖^6 ≤ (432/5)*‖φ‖^4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 1+(N:ℝ))).mpr
    have hh := mul_le_mul_of_nonneg_right hN (pow_nonneg (norm_nonneg φ) 4)
    nlinarith
  linarith

/-- Exact arithmetic behind the source factor 265; the extra factor W is at least one. -/
theorem gap_global_265_budget (q W : ℝ) (hq : 0 ≤ q) (hW : 1 ≤ W) :
    256*Real.pi^2*W^2*q^2+(18*q+(432/5)*q^2) ≤
      265*Real.pi^2*W^2*(1+q)*q := by
  have hW2 : 1 ≤ W^2 := by nlinarith
  have hpi : 432/5 ≤ 9*Real.pi^2 := by nlinarith [Real.pi_gt_d2]
  have hl : 18 ≤ 265*Real.pi^2*W^2 := by
    have hh := mul_le_mul_of_nonneg_left hW2 (by positivity : 0 ≤ 265*Real.pi^2)
    nlinarith [Real.pi_gt_three]
  have hq' : 432/5 ≤ 9*Real.pi^2*W^2 :=
    hpi.trans (by nlinarith [mul_le_mul_of_nonneg_left hW2 (by positivity : 0 ≤ 9*Real.pi^2)])
  have h1 := mul_le_mul_of_nonneg_right hl hq
  have h2 := mul_le_mul_of_nonneg_right hq' (sq_nonneg q)
  nlinarith

end NLS.ZakharovShabat
