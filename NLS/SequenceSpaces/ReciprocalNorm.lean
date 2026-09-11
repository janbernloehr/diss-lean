import NLS.SequenceSpaces.Basic
import NLS.SequenceSpaces.ReciprocalSeries

/-!
# Height-dependent reciprocal sequence norms

The integral estimate of Appendix B.1 gives a `h^(-1/p)` bound for a
reciprocal sequence in the conjugate space. Separating its central coefficient
supplies the additional `1/h` term in Chapter 1, Lemma 3.2(ii).
-/

noncomputable section
open scoped ENNReal

namespace NLS.Coeff

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

omit [Fact (1 ≤ q)] in
/-- A reciprocal envelope with its central coefficient removed has norm at most
`4p * h^(-1/p)` in the conjugate sequence space. -/
theorem norm_punctured_reciprocal_le {p h : ℝ} (hc : p.HolderConjugate q.toReal)
    (hh : 0 < h) (a : Coeff q) (ha0 : a 0 = 0)
    (ha : ∀ k : ℤ, k ≠ 0 → ‖a k‖ ≤ 2 / (h + |(k : ℝ)|)) :
    ‖a‖ ≤ 4 * p * h ^ (-(1 / p)) := by
  have hq := hc.symm.pos
  have hq1 := hc.symm.lt
  have hp := hc.pos
  have hs := ReciprocalSeries.summable_int_shifted_rpow hh.le hc.symm.lt
  have hcoeff : 2 / (q.toReal - 1) ≤ (2 * p) ^ q.toReal := by
    calc
      _ ≤ 2 * p := by
        apply (div_le_iff₀ hc.symm.sub_one_pos).mpr
        nlinarith [hc.symm.sub_one_mul_conj]
      _ ≤ _ := Real.self_le_rpow_of_one_le (by linarith [hc.lt]) hc.symm.lt.le
  have hexp : -(1 / p) * q.toReal = 1 - q.toReal := by
    calc
      _ = -(q.toReal / p) := by ring
      _ = _ := by rw [hc.symm.div_conj_eq_sub_one]; ring
  apply lp.norm_le_of_tsum_le hq (by positivity)
  calc
    (∑' k : ℤ, ‖a k‖ ^ q.toReal) ≤
        ∑' k : ℤ, (2 : ℝ) ^ q.toReal *
          (if k = 0 then 0 else (h + |(k : ℝ)|) ^ (-q.toReal)) := by
      apply Summable.tsum_le_tsum _ ((lp.memℓp a).summable hq) (hs.mul_left _)
      intro k
      by_cases hk : k = 0
      · simp [hk, ha0, hq.ne']
      · rw [if_neg hk]
        calc
          _ ≤ (2 / (h + |(k : ℝ)|)) ^ q.toReal :=
            Real.rpow_le_rpow (norm_nonneg _) (ha k hk) hq.le
          _ = _ := by
            rw [div_eq_mul_inv, Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (by positivity),
              Real.inv_rpow (by positivity : 0 ≤ h + |(k : ℝ)|),
              Real.rpow_neg (by positivity : 0 ≤ h + |(k : ℝ)|)]

    _ = (2 : ℝ) ^ q.toReal * ∑' k : ℤ,
        (if k = 0 then 0 else (h + |(k : ℝ)|) ^ (-q.toReal)) := tsum_mul_left
    _ ≤ (2 : ℝ) ^ q.toReal * (2 / (q.toReal - 1) * h ^ (1 - q.toReal)) :=
      mul_le_mul_of_nonneg_left (ReciprocalSeries.tsum_int_shifted_rpow_le_integral hh hc.symm.lt)
        (by positivity)
    _ ≤ (2 : ℝ) ^ q.toReal * ((2 * p) ^ q.toReal * h ^ (1 - q.toReal)) := by
      gcongr
    _ = (4 * p * h ^ (-(1 / p))) ^ q.toReal := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 4 * p) (by positivity),
        ← Real.rpow_mul hh.le, hexp, ← mul_assoc, ← Real.mul_rpow (by norm_num) (by positivity)]
      congr 2
      ring

/-- Add the central `1/h` contribution to the reciprocal-envelope bound. -/
theorem norm_reciprocal_le {p h : ℝ} (hc : p.HolderConjugate q.toReal)
    (hh : 0 < h) (a : Coeff q) (ha0 : ‖a 0‖ ≤ h⁻¹)
    (ha : ∀ k : ℤ, k ≠ 0 → ‖a k‖ ≤ 2 / (h + |(k : ℝ)|)) :
    ‖a‖ ≤ 4 * p / h ^ (1 / p) + h⁻¹ := by
  let c : Coeff q := lp.single q 0 (a 0)
  let b : Coeff q := a - c
  have hb_apply (k : ℤ) : b k = a k - c k := rfl
  have hc0 : c 0 = a 0 := lp.single_apply_self _ _ _
  have hb0 : b 0 = 0 := by rw [hb_apply, hc0, sub_self]
  have hb : ∀ k : ℤ, k ≠ 0 → ‖b k‖ ≤ 2 / (h + |(k : ℝ)|) := by
    intro k hk
    have hck : c k = 0 := lp.single_apply_ne _ _ _ hk
    rw [hb_apply, hck, sub_zero]
    exact ha k hk
  have hn := norm_punctured_reciprocal_le hc hh b hb0 hb
  have he : a = c + b := by dsimp only [b]; abel
  have hcnorm : ‖c‖ = ‖a 0‖ := lp.norm_single (zero_lt_one.trans_le (show 1 ≤ q from Fact.out)) _ _
  calc
    ‖a‖ = ‖c + b‖ := congrArg norm he
    _ ≤ ‖c‖ + ‖b‖ := norm_add_le _ _
    _ = ‖a 0‖ + ‖b‖ := by rw [hcnorm]
    _ ≤ h⁻¹ + 4 * p * h ^ (-(1 / p)) := add_le_add ha0 hn
    _ = _ := by rw [Real.rpow_neg hh.le]; ring

end NLS.Coeff
