import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.MeanInequalities

/-! # Geometric interpolation of Hilbert coefficient norms

Hölder gives log-convexity for any three coefficient sequences whose pointwise
magnitudes obey the geometric interpolation inequality, including endpoints.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- Pointwise geometric interpolation controls the Hilbert norm with constant one. -/
theorem norm_le_geometric (a b c : Coeff 2) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ ‖a n‖^(1-t)*‖b n‖^t) :
    ‖c‖ ≤ ‖a‖^(1-t)*‖b‖^t := by
  by_cases h0 : t = 0
  · subst t
    simpa using lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) (fun n => by simpa using hc n)
  by_cases h1 : t = 1
  · subst t
    simpa using lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) (fun n => by simpa using hc n)
  have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm h0)
  have ht1' : t < 1 := lt_of_le_of_ne ht1 h1
  let F (n : ℤ) := ‖a n‖^(2*(1-t))
  let G (n : ℤ) := ‖b n‖^(2*t)
  have hF : (fun n => F n ^ (1-t)⁻¹) = fun n => ‖a n‖^(2:ℝ) := by
    funext n
    dsimp only [F]
    rw [← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp [sub_ne_zero.mpr ht1'.ne']
  have hG : (fun n => G n ^ t⁻¹) = fun n => ‖b n‖^(2:ℝ) := by
    funext n
    dsimp only [G]
    rw [← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (Real.HolderConjugate.one_sub_inv_inv ht' ht1')
    (fun n => Real.rpow_nonneg (norm_nonneg (a n)) _)
    (fun n => Real.rpow_nonneg (norm_nonneg (b n)) _)
    (show Summable (fun n => F n ^ (1-t)⁻¹) by rw [hF]; exact (lp.memℓp a).summable (by norm_num))
    (show Summable (fun n => G n ^ t⁻¹) by rw [hG]; exact (lp.memℓp b).summable (by norm_num))
  have hsq : ‖c‖^2 ≤ (‖a‖^(1-t)*‖b‖^t)^2 := by
    calc
      _ = ∑' n : ℤ, ‖c n‖^2 := by
        simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) c
      _ ≤ ∑' n : ℤ, F n*G n := by
        apply Summable.tsum_le_tsum _ _ h.1
        · intro n
          have hn := pow_le_pow_left₀ (norm_nonneg _) (hc n) 2
          simpa only [mul_pow,← Real.rpow_mul_natCast (norm_nonneg _),Nat.cast_ofNat,F,G,mul_comm] using hn
        · simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (lp.memℓp c).summable (by norm_num)
      _ ≤ _ := by
        have hh := h.2
        rw [hF,hG] at hh
        simp only [one_div,inv_inv] at hh
        have hA : (∑' n : ℤ, ‖a n‖^(2:ℝ)) = ‖a‖^(2:ℝ) := by
          simpa only [ENNReal.toReal_ofNat] using (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) a).symm
        have hB : (∑' n : ℤ, ‖b n‖^(2:ℝ)) = ‖b‖^(2:ℝ) := by
          simpa only [ENNReal.toReal_ofNat] using (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) b).symm
        rw [hA,hB] at hh
        simpa only [← Real.rpow_mul (norm_nonneg a),← Real.rpow_mul (norm_nonneg b),
          mul_pow,← Real.rpow_mul_natCast (norm_nonneg _),Nat.cast_ofNat,F,G,mul_comm] using hh
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (by positivity))).mp hsq

end NLS.Coeff
