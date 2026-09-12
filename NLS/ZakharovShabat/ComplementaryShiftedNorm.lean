import NLS.ZakharovShabat.ComplementaryFreeInverse
import NLS.SequenceSpaces.ShiftedPairNorm

/-!
# Uniform complementary inverse bounds in every signed shifted norm

Pointwise coefficient domination passes to the weighted scalar and finite-`p`
pair norms, including after opposite physical modulations. Consequently the
resonant projections and complementary free inverse are contractions in every
shifted norm, with a constant independent of the shift and the strip index.
-/

noncomputable section
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Raw coefficient norm domination implies domination in every positive weighted norm. -/
theorem WeightedCoeff.norm_mono {w : Weight} {a b : WeightedCoeff w p}
    (h : ∀ k, ‖a.val k‖ ≤ ‖b.val k‖) : ‖a‖ ≤ ‖b‖ := by
  rw [WeightedCoeff.norm_eq, WeightedCoeff.norm_eq]
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro k
  simp only [WeightedCoeff.weightEquiv_apply, norm_mul]
  exact mul_le_mul_of_nonneg_left (h k) (norm_nonneg _)

/-- Component norm domination respects the exact finite-exponent pair norm. -/
theorem WeightedCoeffPair.norm_mono (hp : p ≠ ⊤) {w : Weight} {a b : WeightedCoeffPair w p}
    (h₁ : ‖a.fst‖ ≤ ‖b.fst‖) (h₂ : ‖a.snd‖ ≤ ‖b.snd‖) : ‖a‖ ≤ ‖b‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  rw [WithLp.prod_norm_eq_add hp0, WithLp.prod_norm_eq_add hp0]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact add_le_add (Real.rpow_le_rpow (norm_nonneg _) h₁ hp0.le)
    (Real.rpow_le_rpow (norm_nonneg _) h₂ hp0.le)

/-- Coefficient domination remains valid after any physical modulation. -/
theorem SpectralWeight.shiftedNorm_mono (w : SpectralWeight) (i : ℤ)
    {a b : WeightedCoeff w.toWeight p} (h : ∀ k, ‖a.val k‖ ≤ ‖b.val k‖) :
    w.shiftedNorm i a ≤ w.shiftedNorm i b := by
  rw [← w.norm_modulation, ← w.norm_modulation]
  apply WeightedCoeff.norm_mono
  intro k
  simpa only [SpectralWeight.modulation_apply] using h (k - i)

/-- Opposite shifts of the two physical components preserve coefficient domination. -/
theorem SpectralWeight.shiftedPairNorm_mono (w : SpectralWeight) (hp : p ≠ ⊤) (i : ℤ)
    {a b : WeightedCoeffPair w.toWeight p}
    (h₁ : ∀ k, ‖a.fst.val k‖ ≤ ‖b.fst.val k‖) (h₂ : ∀ k, ‖a.snd.val k‖ ≤ ‖b.snd.val k‖) :
    w.shiftedPairNorm i a ≤ w.shiftedPairNorm i b := by
  apply WeightedCoeffPair.norm_mono hp
  · change ‖w.modulation (-i) a.fst‖ ≤ ‖w.modulation (-i) b.fst‖
    simpa only [SpectralWeight.norm_modulation] using w.shiftedNorm_mono (-i) h₁
  · change ‖w.modulation i a.snd‖ ≤ ‖w.modulation i b.snd‖
    simpa only [SpectralWeight.norm_modulation] using w.shiftedNorm_mono i h₂

namespace ZakharovShabat

theorem shiftedPairNorm_resonantProjection_le (w : SpectralWeight) (hp : p ≠ ⊤) (n i : ℤ)
    (a : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm i (resonantProjection w.toWeight n a) ≤ w.shiftedPairNorm i a := by
  apply w.shiftedPairNorm_mono hp i <;> intro k
  · rw [resonantProjection_fst]; split_ifs <;> simp
  · rw [resonantProjection_snd]; split_ifs <;> simp

theorem shiftedPairNorm_complementaryProjection_le (w : SpectralWeight) (hp : p ≠ ⊤) (n i : ℤ)
    (a : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm i (complementaryProjection w.toWeight n a) ≤ w.shiftedPairNorm i a := by
  apply w.shiftedPairNorm_mono hp i <;> intro k
  · rw [complementaryProjection_fst]; split_ifs <;> simp
  · rw [complementaryProjection_snd]; split_ifs <;> simp

/-- `A_λ⁻¹ Q_n` is a contraction uniformly in `n`, `λ∈U_n`, and every signed shift. -/
theorem shiftedPairNorm_complementaryFreeInverse_le (w : SpectralWeight) (hp : p ≠ ⊤) (n i : ℤ)
    (z : ℂ) (hz : z ∈ resonantStrip n) (a : WeightedCoeffPair w.toWeight p) :
    w.shiftedPairNorm i (complementaryFreeInverse w.toWeight n z hz a) ≤ w.shiftedPairNorm i a := by
  apply w.shiftedPairNorm_mono hp i <;> intro k
  · rw [complementaryFreeInverse_fst, norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (norm_complementarySymbol_le hz (-k)) (norm_nonneg (a.fst.val k))
  · rw [complementaryFreeInverse_snd, norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (norm_complementarySymbol_le hz k) (norm_nonneg (a.snd.val k))

end ZakharovShabat
end NLS
