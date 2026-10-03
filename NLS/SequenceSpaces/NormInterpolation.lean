import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.MeanInequalities

/-! # Interpolation of sequence norms on one coefficient function

Hölder applied to powers of the same sequence gives the quantitative
intermediate norm bound. The coefficient equalities are explicit, so the
estimate can be used across independently constructed Fourier realizations.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- Quantitative interpolation between two finite sequence exponents. -/
theorem norm_interpolate
    {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (hp : 0 < p.toReal) (hq : 0 < q.toReal) (hr : 0 < r.toReal)
    (a : Coeff p) (b : Coeff q) (c : Coeff r)
    (ha : ∀ n : ℤ, a n = c n) (hb : ∀ n : ℤ, b n = c n)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (he : r.toReal = p.toReal*(1-t)+q.toReal*t) :
    ‖c‖ ≤ ‖a‖^(p.toReal*(1-t)/r.toReal)*‖b‖^(q.toReal*t/r.toReal) := by
  let F (n : ℤ) := ‖c n‖^(p.toReal*(1-t))
  let G (n : ℤ) := ‖c n‖^(q.toReal*t)
  have hF : (fun n => F n ^ (1-t)⁻¹) = fun n => ‖a n‖^p.toReal := by
    funext n
    dsimp only [F]
    rw [← Real.rpow_mul (norm_nonneg _),← ha n]
    congr 1
    field_simp [sub_ne_zero.mpr ht1.ne']
  have hG : (fun n => G n ^ t⁻¹) = fun n => ‖b n‖^q.toReal := by
    funext n
    dsimp only [G]
    rw [← Real.rpow_mul (norm_nonneg _),← hb n]
    congr 1
    field_simp
  have hFG : (fun n => F n*G n) = fun n => ‖c n‖^r.toReal := by
    funext n
    dsimp only [F,G]
    rw [← Real.rpow_add_of_nonneg (norm_nonneg _) (by positivity) (by positivity),← he]
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    (Real.HolderConjugate.one_sub_inv_inv ht ht1)
    (fun n => Real.rpow_nonneg (norm_nonneg (c n)) _) (fun n => Real.rpow_nonneg (norm_nonneg (c n)) _)
    (show Summable (fun n => F n ^ (1-t)⁻¹) by rw [hF]; exact (lp.memℓp a).summable hp)
    (show Summable (fun n => G n ^ t⁻¹) by rw [hG]; exact (lp.memℓp b).summable hq)
  rw [hFG,hF,hG,← lp.norm_rpow_eq_tsum hp a,← lp.norm_rpow_eq_tsum hq b,
    ← lp.norm_rpow_eq_tsum hr c] at h
  simp only [one_div,inv_inv] at h
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg c) r.toReal) h (inv_nonneg.mpr hr.le)
  rw [← Real.rpow_mul (norm_nonneg c),mul_inv_cancel₀ hr.ne',Real.rpow_one,
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (norm_nonneg a),← Real.rpow_mul (norm_nonneg b),
    ← Real.rpow_mul (norm_nonneg a),← Real.rpow_mul (norm_nonneg b)] at hh
  simpa only [div_eq_mul_inv,mul_assoc] using hh

/-- Interpolation transfers an inverse-scale endpoint bound to a fractional decay rate.
The weaker exponent `t` is convenient when the intermediate exponent is at most the upper one. -/
theorem norm_interpolate_decay
    {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (hp : 0 < p.toReal) (hq : 0 < q.toReal) (hr : 0 < r.toReal) (hrq : r.toReal ≤ q.toReal)
    (a : Coeff p) (b : Coeff q) (c : Coeff r)
    (ha : ∀ n : ℤ, a n = c n) (hb : ∀ n : ℤ, b n = c n)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (he : r.toReal = p.toReal*(1-t)+q.toReal*t)
    (K d : ℝ) (hK : 0 ≤ K) (hd : 1 ≤ d) (hA : ‖a‖ ≤ K) (hB : ‖b‖ ≤ K/d) :
    ‖c‖ ≤ K/d^t := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hα : 0 ≤ p.toReal*(1-t)/r.toReal := by positivity
  have hβ : 0 ≤ q.toReal*t/r.toReal := by positivity
  have hab : p.toReal*(1-t)/r.toReal+q.toReal*t/r.toReal = 1 := by
    rw [← add_div,← he,div_self hr.ne']
  have htb : t ≤ q.toReal*t/r.toReal := by
    apply (le_div_iff₀ hr).mpr
    nlinarith
  calc
    _ ≤ ‖a‖^(p.toReal*(1-t)/r.toReal)*‖b‖^(q.toReal*t/r.toReal) :=
      norm_interpolate hp hq hr a b c ha hb t ht ht1 he
    _ ≤ K^(p.toReal*(1-t)/r.toReal)*(K/d)^(q.toReal*t/r.toReal) := by gcongr
    _ = K/d^(q.toReal*t/r.toReal) := by
      rw [Real.div_rpow hK hd0.le,← mul_div_assoc,
        ← Real.rpow_add_of_nonneg hK hα hβ,hab,Real.rpow_one]
    _ ≤ K/d^t := div_le_div_of_nonneg_left hK (Real.rpow_pos_of_pos hd0 _)
      (Real.rpow_le_rpow_of_exponent_le hd htb)

/-- A common coefficient family interpolates across the closed interval `[p,2]`.
Using one real-indexed family avoids changing its realization at either endpoint. -/
theorem norm_interpolate_decay_family
    (a : (s : ℝ) → (1 < s) → Coeff (ENNReal.ofReal s))
    (p r : ℝ) (hp : 1 < p) (hp2 : p < 2) (hrp : p ≤ r) (hr2 : r ≤ 2)
    (heq : ∀ s hs n, a s hs n = a r (lt_of_lt_of_le hp hrp) n)
    (K d : ℝ) (hK : 0 ≤ K) (hd : 1 ≤ d)
    (hA : ‖a p hp‖ ≤ K) (hB : ‖a 2 (by norm_num)‖ ≤ K/d) :
    ‖a r (lt_of_lt_of_le hp hrp)‖ ≤ K/d^((r-p)/(2-p)) := by
  by_cases hr0 : r = p
  · subst r
    simpa only [sub_self,zero_div,Real.rpow_zero,div_one] using hA
  by_cases hr1 : r = 2
  · subst r
    simpa only [div_self (sub_ne_zero.mpr hp2.ne'),Real.rpow_one] using hB
  have hrp' : p < r := lt_of_le_of_ne hrp (Ne.symm hr0)
  have hr2' : r < 2 := lt_of_le_of_ne hr2 hr1
  have hr : 1 < r := lt_of_lt_of_le hp hrp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨ENNReal.one_le_ofReal.mpr hr.le⟩
  let : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have ht : 0 < (r-p)/(2-p) := div_pos (sub_pos.mpr hrp') (sub_pos.mpr hp2)
  have ht1 : (r-p)/(2-p) < 1 := (div_lt_one (sub_pos.mpr hp2)).mpr (by linarith)
  apply norm_interpolate_decay
    (p := ENNReal.ofReal p) (q := ENNReal.ofReal (2 : ℝ)) (r := ENNReal.ofReal r)
    (by simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using (show 0 < p by linarith))
    (by norm_num)
    (by simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ r)] using (show 0 < r by linarith))
    (by simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ r),ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using hr2)
    (a p hp) (a 2 (by norm_num)) (a r hr) (heq p hp) (heq 2 (by norm_num))
    ((r-p)/(2-p)) ht ht1 _ K d hK hd hA hB
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ p),
    ENNReal.toReal_ofReal (by linarith : 0 ≤ r),ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [sub_ne_zero.mpr hp2.ne']
  ring

end NLS.Coeff
