import NLS.ZakharovShabat.DiagonalSupSummability
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Quantitative diagonal tail sums

The conjugate identity turns the reciprocal norm decay into the source power
`min(1,p-1)`. The explicit constant depends only on the exponent.
-/

noncomputable section
open scoped ENNReal NNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An explicit admissible constant for Lemma 6.8(i). -/
def diagonalSummationConstant (p : ℝ≥0∞) : ℝ :=
  (8 * max p.toReal p.conjExponent.toReal) ^ p.toReal * 2 ^ (p.toReal-1)

omit [Fact (1 ≤ p)] in
theorem diagonalSummationConstant_nonneg : 0 ≤ diagonalSummationConstant p := by
  unfold diagonalSummationConstant
  positivity

omit [Fact (1 ≤ p)] in
/-- Raising the row-tail bound gives exactly the required decay exponent. -/
theorem diagonal_tail_power_le {s A B T : ℝ} (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hs0 : 0 ≤ s) (hs : s ≤ max p.toReal p.conjExponent.toReal)
    (he : p.toReal/s = min 1 (p.toReal-1)) (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (N : ℕ) :
    (8*s*B * (A*(N : ℝ)^(-(1/s))+T)) ^ p.toReal ≤
      diagonalSummationConstant p * B^p.toReal *
        (A^p.toReal / (N : ℝ)^(min 1 (p.toReal-1)) + T^p.toReal) := by
  have hP : 1 ≤ p.toReal := by
    exact (ENNReal.toReal_le_toReal (by simp) hp).mpr hp1.le
  have hsum : (A*(N : ℝ)^(-(1/s))+T)^p.toReal ≤
      (2 : ℝ)^(p.toReal-1) * ((A*(N : ℝ)^(-(1/s)))^p.toReal + T^p.toReal) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
      (⟨A*(N : ℝ)^(-(1/s)), by positivity⟩ : ℝ≥0) (⟨T,hT⟩ : ℝ≥0) hP
  have hdecay : ((N : ℝ)^(-(1/s)))^p.toReal = ((N : ℝ)^(min 1 (p.toReal-1)))⁻¹ := by
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    have hexp : -(1/s)*p.toReal = -(min 1 (p.toReal-1)) := by rw [← he]; ring
    rw [hexp, Real.rpow_neg (Nat.cast_nonneg N)]
  calc
    _ ≤ (8 * max p.toReal p.conjExponent.toReal * B * (A*(N : ℝ)^(-(1/s))+T))^p.toReal := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (by norm_num)) hB) (by positivity)
    _ = (8 * max p.toReal p.conjExponent.toReal)^p.toReal * B^p.toReal *
        (A*(N : ℝ)^(-(1/s))+T)^p.toReal := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hB]
    _ ≤ (8 * max p.toReal p.conjExponent.toReal)^p.toReal * B^p.toReal *
        ((2 : ℝ)^(p.toReal-1) * ((A*(N : ℝ)^(-(1/s)))^p.toReal + T^p.toReal)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hA (by positivity), hdecay]
      unfold diagonalSummationConstant
      rw [div_eq_mul_inv]
      ring

/-- The actual high-frequency diagonal sum has the source decay and separate component tails. -/
theorem diagonalSup_tail_sum_le (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 0 < N)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ resonantDiagonalSup hp w φ n ∧
      resonantDiagonalSup hp w φ n ≤ resonantDiagonalBound hp w φ n) :
    (∑' n : ℤ, if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0) ≤
      diagonalSummationConstant p * ‖w.forgetWeight φ.fst‖^p.toReal *
        (‖w.toCoeff φ.snd‖^p.toReal / (N : ℝ)^(min 1 (p.toReal-1)) +
          ‖Coeff.fourierTail N (w.toCoeff φ.snd)‖^p.toReal) := by
  obtain ⟨s, hc, hs, he, v, hv, hn⟩ := exists_diagonalSupTail hp hp1 w φ N hN hb
  have hP : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have heq : (∑' n : ℤ, if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0) = ‖v‖^p.toReal := by
    rw [lp.norm_rpow_eq_tsum hP]
    apply tsum_congr
    intro n
    rw [hv]
    split_ifs with h
    · rw [Complex.norm_real, Real.norm_of_nonneg (hb n h).1]
    · simp [Real.zero_rpow hP.ne']
  rw [heq]
  exact (Real.rpow_le_rpow (norm_nonneg _) hn hP.le).trans
    (diagonal_tail_power_le hp hp1 hc.pos.le hs he (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) N)

end NLS.ZakharovShabat
