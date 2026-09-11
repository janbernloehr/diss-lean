import NLS.SequenceSpaces.SobolevEmbedding
import NLS.SequenceSpaces.ReciprocalSeries

/-!
# A numerical bound for the Sobolev embedding constant

Appendix B.1 bounds the reciprocal one-derivative weight in the Hölder
conjugate space. In particular, the previously explicit sequence-space
constant is at most `2p` for every finite Banach exponent `p`.
-/

noncomputable section
open scoped ENNReal

namespace NLS

private theorem tsum_bracket_rpow_le {q : ℝ} (hq : 1 < q) :
    (∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-q)) ≤ 1 + 2 / (q - 1) := by
  have hs : Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-q)) := by
    apply (summable_inverse_bracket hq).congr
    intro n
    rw [Real.rpow_neg (by positivity), one_div]
  rw [hs.tsum_eq_add_tsum_ite 0]
  have h := ReciprocalSeries.tsum_int_shifted_rpow_le_integral (α := 1) (by norm_num) hq
  simp only [Int.cast_zero, abs_zero, add_zero, Real.one_rpow, mul_one] at h ⊢
  linarith

namespace WeightedCoeff

private theorem norm_inverse_weight (n : ℤ) :
    ‖(Weight.sobolev 1 n : ℂ)⁻¹‖ = (1 + |(n : ℝ)|)⁻¹ := by
  simp only [Weight.sobolev_apply, Real.rpow_one, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + |(n : ℝ)|)]

/-- The inverse Sobolev weight has conjugate norm at most `2p`, including `p=1`. -/
theorem norm_inverse_sobolev_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp : p ≠ ⊤)
    (hw : Memℓp (fun n => (Weight.sobolev 1 n : ℂ)⁻¹) q) :
    ‖inverseWeight (Weight.sobolev 1) hw‖ ≤ 2 * p.toReal := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  by_cases hq : q = ⊤
  · subst q
    apply (lp.norm_le_of_forall_le zero_le_one (fun n => ?_)).trans (by linarith : 1 ≤ 2 * p.toReal)
    change ‖(Weight.sobolev 1 n : ℂ)⁻¹‖ ≤ 1
    rw [norm_inverse_weight]
    exact inv_le_one_of_one_le₀ (by linarith [abs_nonneg (n : ℝ)])
  · have hc := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
    have hqpos := hc.symm.pos
    have hnorm : ∑' n : ℤ, ‖inverseWeight (Weight.sobolev 1) hw n‖ ^ q.toReal =
        ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-q.toReal) := by
      apply tsum_congr
      intro n
      change ‖(Weight.sobolev 1 n : ℂ)⁻¹‖ ^ q.toReal = _
      rw [norm_inverse_weight, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
    apply lp.norm_le_of_tsum_le hqpos (by positivity)
    rw [hnorm]
    calc
      _ ≤ 1 + 2 / (q.toReal - 1) := tsum_bracket_rpow_le hc.symm.lt
      _ ≤ 2 * p.toReal := by
        have hd : 2 / (q.toReal - 1) ≤ 2 * p.toReal - 1 := by
          apply (div_le_iff₀ hc.symm.sub_one_pos).mpr
          nlinarith [hc.symm.sub_one_mul_conj]
        linarith
      _ ≤ (2 * p.toReal) ^ q.toReal :=
        Real.self_le_rpow_of_one_le (by linarith) hc.symm.lt.le

/-- A numerical form of the previously defined embedding constant. -/
theorem sobolevEmbeddingConstant_le_two_mul (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    sobolevEmbeddingConstant p hp ≤ 2 * p.toReal := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  exact norm_inverse_sobolev_le hp _

end WeightedCoeff
end NLS
