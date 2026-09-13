import NLS.ZakharovShabat.OffDiagonalPower
import NLS.SequenceSpaces.HalfCutoffPower
import NLS.SequenceSpaces.SpectralReflectionTail

/-!
# Off-diagonal power sums in the source pair norm

The regional bound gives the decay `min(1,p-1)` at the full cutoff and a
product of two potential tails. Component norm bounds give the pair norm
and its half-cutoff tail, retaining the distinguished component factor.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- An exponent-only constant for the weighted off-diagonal source estimate. -/
def offDiagonalSummationConstant (p : ℝ≥0∞) : ℝ := 3 * offDiagonalRegionConstant p

theorem offDiagonalRegionConstant_nonneg (p : ℝ≥0∞) : 0 ≤ offDiagonalRegionConstant p := by
  unfold offDiagonalRegionConstant doubleReciprocalSummationConstant
  positivity

theorem offDiagonalSummationConstant_nonneg (p : ℝ≥0∞) : 0 ≤ offDiagonalSummationConstant p :=
  mul_nonneg (by norm_num) (offDiagonalRegionConstant_nonneg p)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Common bounds on the two potential norms and tails yield the pair-shaped estimate. -/
theorem offDiagonalTailBound_sum_le_of_norm_bounds (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (d a : WeightedCoeff w.toWeight p) (N : ℕ) (hN : 2 ≤ N)
    (B R : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R) (hd : ‖d‖ ≤ B) (ha : ‖a‖ ≤ B)
    (htd : ‖WeightedCoeff.fourierTail w.toWeight N d‖ ≤ R)
    (hta : ‖WeightedCoeff.fourierTail w.toWeight N a‖ ≤ R) :
    (∑' n : ℤ, (offDiagonalTailBound hp w d a N n)^p.toReal) ≤
      offDiagonalSummationConstant p * ‖d‖^p.toReal *
        (B^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) + R^(2*p.toReal)) := by
  have hP : 1 ≤ p.toReal := (ENNReal.toReal_le_toReal (by simp) hp).mpr hp1.le
  have hhalf := one_div_halfCutoff_rpow_le (by positivity : 0 ≤ min 1 (p.toReal-1))
    (min_le_left _ _) N hN
  have hprod : ‖d‖^p.toReal * ‖a‖^p.toReal ≤ B^(2*p.toReal) := by
    calc
      _ ≤ B^p.toReal * B^p.toReal := mul_le_mul
        (Real.rpow_le_rpow (norm_nonneg _) hd ENNReal.toReal_nonneg)
        (Real.rpow_le_rpow (norm_nonneg _) ha ENNReal.toReal_nonneg) (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add' hB (by positivity : p.toReal + p.toReal ≠ 0)]; congr 1; ring
  have htail : ‖WeightedCoeff.fourierTail w.toWeight N d‖^p.toReal *
      ‖WeightedCoeff.fourierTail w.toWeight N a‖^p.toReal ≤ R^(2*p.toReal) := by
    calc
      _ ≤ R^p.toReal * R^p.toReal := mul_le_mul
        (Real.rpow_le_rpow (norm_nonneg _) htd ENNReal.toReal_nonneg)
        (Real.rpow_le_rpow (norm_nonneg _) hta ENNReal.toReal_nonneg) (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add' hR (by positivity : p.toReal + p.toReal ≠ 0)]; congr 1; ring
  apply (offDiagonalTailBound_summable_and_le hp hp1 w d a N hN).2.trans
  calc
    _ ≤ offDiagonalRegionConstant p * ‖d‖^p.toReal *
        (B^(2*p.toReal) * (3 / (N : ℝ)^(min 1 (p.toReal-1))) + R^(2*p.toReal)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (offDiagonalRegionConstant_nonneg p) (by positivity))
      apply add_le_add _ htail
      rw [div_eq_mul_one_div]
      exact mul_le_mul hprod hhalf (by positivity) (by positivity)
    _ ≤ offDiagonalSummationConstant p * ‖d‖^p.toReal *
        (B^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) + R^(2*p.toReal)) := by
      unfold offDiagonalSummationConstant
      have hc := offDiagonalRegionConstant_nonneg p
      have hr : 0 ≤ R^(2*p.toReal) := by positivity
      have hdP : 0 ≤ ‖d‖^p.toReal := by positivity
      simp only [div_eq_mul_inv] at *
      nlinarith [mul_nonneg (mul_nonneg hc hdP) hr]

/-- Each weighted component tail at `N` is bounded by the pair tail at `N/2`. -/
theorem norm_offDiagonal_componentTails_le (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) :
    ‖WeightedCoeff.fourierTail w.toWeight N φ.fst‖ ≤ ‖weightedPairFourierTail w.toWeight (N/2) φ‖ ∧
    ‖WeightedCoeff.fourierTail w.toWeight N φ.snd‖ ≤ ‖weightedPairFourierTail w.toWeight (N/2) φ‖ := by
  exact ⟨(w.norm_fourierTail_antitone φ.fst (Nat.div_le_self N 2)).trans
      (WithLp.norm_fst_le _ (weightedPairFourierTail w.toWeight (N/2) φ)),
    (w.norm_fourierTail_antitone φ.snd (Nat.div_le_self N 2)).trans
      (WithLp.norm_snd_le _ (weightedPairFourierTail w.toWeight (N/2) φ))⟩

/-- Source pair bound for the negative coefficient majorant. -/
theorem offDiagonalTailBound_minus_sum_le_pair (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 2 ≤ N) :
    (∑' n : ℤ, (offDiagonalTailBound hp w (w.reflection φ.fst) φ.snd N n)^p.toReal) ≤
      offDiagonalSummationConstant p * ‖φ.fst‖^p.toReal *
        (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
          ‖weightedPairFourierTail w.toWeight (N/2) φ‖^(2*p.toReal)) := by
  have hd : ‖w.reflection φ.fst‖ ≤ ‖φ‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact WithLp.norm_fst_le _ φ
  have htd : ‖WeightedCoeff.fourierTail w.toWeight N (w.reflection φ.fst)‖ ≤
      ‖weightedPairFourierTail w.toWeight (N/2) φ‖ := by
    rw [w.norm_fourierTail_reflection]
    exact (norm_offDiagonal_componentTails_le w φ N).1
  simpa only [LinearIsometryEquiv.norm_map] using
    offDiagonalTailBound_sum_le_of_norm_bounds hp hp1 w (w.reflection φ.fst) φ.snd N hN
      ‖φ‖ ‖weightedPairFourierTail w.toWeight (N/2) φ‖ (norm_nonneg _) (norm_nonneg _)
      hd (WithLp.norm_snd_le _ φ) htd (norm_offDiagonal_componentTails_le w φ N).2

/-- Source pair bound for the positive coefficient majorant. -/
theorem offDiagonalTailBound_plus_sum_le_pair (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 2 ≤ N) :
    (∑' n : ℤ, (offDiagonalTailBound hp w φ.snd (w.reflection φ.fst) N n)^p.toReal) ≤
      offDiagonalSummationConstant p * ‖φ.snd‖^p.toReal *
        (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
          ‖weightedPairFourierTail w.toWeight (N/2) φ‖^(2*p.toReal)) := by
  have ha : ‖w.reflection φ.fst‖ ≤ ‖φ‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact WithLp.norm_fst_le _ φ
  have hta : ‖WeightedCoeff.fourierTail w.toWeight N (w.reflection φ.fst)‖ ≤
      ‖weightedPairFourierTail w.toWeight (N/2) φ‖ := by
    rw [w.norm_fourierTail_reflection]
    exact (norm_offDiagonal_componentTails_le w φ N).1
  exact offDiagonalTailBound_sum_le_of_norm_bounds hp hp1 w φ.snd (w.reflection φ.fst) N hN
    ‖φ‖ ‖weightedPairFourierTail w.toWeight (N/2) φ‖ (norm_nonneg _) (norm_nonneg _)
    (WithLp.norm_snd_le _ φ) ha (norm_offDiagonal_componentTails_le w φ N).2 hta

end NLS.ZakharovShabat
