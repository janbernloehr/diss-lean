import NLS.SequenceSpaces.ConjugateDuality
import Mathlib.Analysis.MeanInequalities

/-!
# The finite trilinear estimate behind Young's convolution inequality

For inverse exponents summing to two, weighted arithmetic-geometric mean
bounds the three-factor kernel by three products of coefficient energies.
Translation of the test sequence then bounds every finite double sum by one
on the three unit balls. This retains the exact constant in Lemma B.2.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- The elementary weighted estimate used to prove Young's inequality by duality. -/
theorem young_pointwise {p q t : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (ht : 1 ≤ t)
    (h : 1 / p + 1 / q + 1 / t = 2) {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * y * z ≤ (1 - 1 / p) * (y ^ q * z ^ t) +
      (1 - 1 / q) * (x ^ p * z ^ t) + (1 - 1 / t) * (x ^ p * y ^ q) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hα : 0 ≤ 1 - 1 / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp)
  have hβ : 0 ≤ 1 - 1 / q := sub_nonneg.mpr ((div_le_one hq0).mpr hq)
  have hγ : 0 ≤ 1 - 1 / t := sub_nonneg.mpr ((div_le_one ht0).mpr ht)
  have hn : 0 ≤ (1 - 1 / p) * (y ^ q * z ^ t) +
      (1 - 1 / q) * (x ^ p * z ^ t) + (1 - 1 / t) * (x ^ p * y ^ q) := by positivity
  rcases hx.eq_or_lt with rfl | hx
  · simpa using hn
  rcases hy.eq_or_lt with rfl | hy
  · simpa using hn
  rcases hz.eq_or_lt with rfl | hz
  · simpa using hn
  have hex : p * (1 - 1 / q) + p * (1 - 1 / t) = 1 := by
    rw [← mul_add, show (1 - 1 / q) + (1 - 1 / t) = 1 / p by linarith]
    exact mul_one_div_cancel hp0.ne'
  have hey : q * (1 - 1 / p) + q * (1 - 1 / t) = 1 := by
    rw [← mul_add, show (1 - 1 / p) + (1 - 1 / t) = 1 / q by linarith]
    exact mul_one_div_cancel hq0.ne'
  have hez : t * (1 - 1 / p) + t * (1 - 1 / q) = 1 := by
    rw [← mul_add, show (1 - 1 / p) + (1 - 1 / q) = 1 / t by linarith]
    exact mul_one_div_cancel ht0.ne'
  have he : (y ^ q * z ^ t) ^ (1 - 1 / p) *
      (x ^ p * z ^ t) ^ (1 - 1 / q) * (x ^ p * y ^ q) ^ (1 - 1 / t) = x * y * z := by
    simp only [Real.mul_rpow (by positivity : 0 ≤ y ^ q) (by positivity : 0 ≤ z ^ t),
      Real.mul_rpow (by positivity : 0 ≤ x ^ p) (by positivity : 0 ≤ z ^ t),
      Real.mul_rpow (by positivity : 0 ≤ x ^ p) (by positivity : 0 ≤ y ^ q),
      ← Real.rpow_mul hx.le, ← Real.rpow_mul hy.le, ← Real.rpow_mul hz.le]
    calc
      _ = (x ^ (p * (1 - 1 / q)) * x ^ (p * (1 - 1 / t))) *
          (y ^ (q * (1 - 1 / p)) * y ^ (q * (1 - 1 / t))) *
          (z ^ (t * (1 - 1 / p)) * z ^ (t * (1 - 1 / q))) := by ring
      _ = _ := by rw [← Real.rpow_add hx, ← Real.rpow_add hy, ← Real.rpow_add hz,
        hex, hey, hez, Real.rpow_one, Real.rpow_one, Real.rpow_one]
  rw [← he]
  exact Real.geom_mean_le_arith_mean3_weighted hα hβ hγ
    (by positivity) (by positivity) (by positivity) (by linarith)

/-- A finite energy sum of a translated sequence is bounded by its whole norm energy. -/
theorem sum_translated_energy_le {p : ℝ≥0∞} (hp : 0 < p.toReal)
    (a : Coeff p) (S : Finset ℤ) (k : ℤ) :
    ∑ n ∈ S, ‖a (n + k)‖ ^ p.toReal ≤ ‖a‖ ^ p.toReal := by
  have hs := (lp.memℓp a).summable hp
  calc
    _ ≤ ∑' n : ℤ, ‖a (n + k)‖ ^ p.toReal :=
      (hs.comp_injective (fun _ _ h => add_right_cancel h)).sum_le_tsum S
        (fun _ _ => by positivity)
    _ = ∑' n : ℤ, ‖a n‖ ^ p.toReal :=
      (Equiv.addRight k).tsum_eq (fun n => ‖a n‖ ^ p.toReal)
    _ = _ := (lp.hasSum_norm hp a).tsum_eq

/-- On three unit balls, every finite convolution pairing has bound one. -/
theorem norm_young_trilinear_unit {p q t : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ t)]
    (hp : 1 ≤ p.toReal) (hq : 1 ≤ q.toReal) (ht : 1 ≤ t.toReal)
    (h : 1 / p.toReal + 1 / q.toReal + 1 / t.toReal = 2)
    (a : Coeff p) (b : Coeff q) (c : Coeff t)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (S T : Finset ℤ) :
    ‖∑ j ∈ S, ∑ k ∈ T, a j * b k * c (j + k)‖ ≤ 1 := by
  have hp0 := zero_lt_one.trans_le hp
  have hq0 := zero_lt_one.trans_le hq
  have ht0 := zero_lt_one.trans_le ht
  have heA : ∑ j ∈ S, ‖a j‖ ^ p.toReal ≤ 1 :=
    (lp.sum_rpow_le_norm_rpow hp0 a S).trans (Real.rpow_le_one (norm_nonneg _) ha hp0.le)
  have heB : ∑ k ∈ T, ‖b k‖ ^ q.toReal ≤ 1 :=
    (lp.sum_rpow_le_norm_rpow hq0 b T).trans (Real.rpow_le_one (norm_nonneg _) hb hq0.le)
  have heC (U : Finset ℤ) (m : ℤ) : ∑ n ∈ U, ‖c (n + m)‖ ^ t.toReal ≤ 1 :=
    (sum_translated_energy_le ht0 c U m).trans (Real.rpow_le_one (norm_nonneg _) hc ht0.le)
  have hBC : ∑ j ∈ S, ∑ k ∈ T, ‖b k‖ ^ q.toReal * ‖c (j + k)‖ ^ t.toReal ≤ 1 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ k ∈ T, ‖b k‖ ^ q.toReal * 1 := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (heC S k) (by positivity)
      _ ≤ _ := by simpa only [mul_one] using heB
  have hAC : ∑ j ∈ S, ∑ k ∈ T, ‖a j‖ ^ p.toReal * ‖c (j + k)‖ ^ t.toReal ≤ 1 := by
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ j ∈ S, ‖a j‖ ^ p.toReal * 1 := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [add_comm] using heC T j
      _ ≤ _ := by simpa only [mul_one] using heA
  have hAB : ∑ j ∈ S, ∑ k ∈ T, ‖a j‖ ^ p.toReal * ‖b k‖ ^ q.toReal ≤ 1 := by
    rw [← Finset.sum_mul_sum]
    exact mul_le_one₀ heA (by positivity) heB
  have hα : 0 ≤ 1 - 1 / p.toReal := sub_nonneg.mpr ((div_le_one hp0).mpr hp)
  have hβ : 0 ≤ 1 - 1 / q.toReal := sub_nonneg.mpr ((div_le_one hq0).mpr hq)
  have hγ : 0 ≤ 1 - 1 / t.toReal := sub_nonneg.mpr ((div_le_one ht0).mpr ht)
  calc
    _ ≤ ∑ j ∈ S, ∑ k ∈ T, ‖a j‖ * ‖b k‖ * ‖c (j + k)‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      simpa only [norm_mul] using norm_sum_le T (fun k => a j * b k * c (j + k))
    _ ≤ ∑ j ∈ S, ∑ k ∈ T,
        ((1 - 1 / p.toReal) * (‖b k‖ ^ q.toReal * ‖c (j + k)‖ ^ t.toReal) +
        (1 - 1 / q.toReal) * (‖a j‖ ^ p.toReal * ‖c (j + k)‖ ^ t.toReal) +
        (1 - 1 / t.toReal) * (‖a j‖ ^ p.toReal * ‖b k‖ ^ q.toReal)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact young_pointwise hp hq ht h (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    _ ≤ (1 - 1 / p.toReal) * 1 + (1 - 1 / q.toReal) * 1 + (1 - 1 / t.toReal) * 1 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [← Finset.mul_sum] at hBC hAC hAB
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hBC hα)
        (mul_le_mul_of_nonneg_left hAC hβ)) (mul_le_mul_of_nonneg_left hAB hγ)
    _ = 1 := by linarith

/-- Homogeneous form of the finite trilinear convolution estimate. -/
theorem norm_young_trilinear_le {p q t : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ t)]
    (hp : 1 ≤ p.toReal) (hq : 1 ≤ q.toReal) (ht : 1 ≤ t.toReal)
    (h : 1 / p.toReal + 1 / q.toReal + 1 / t.toReal = 2)
    (a : Coeff p) (b : Coeff q) (c : Coeff t) (S T : Finset ℤ) :
    ‖∑ j ∈ S, ∑ k ∈ T, a j * b k * c (j + k)‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
  by_cases ha : a = 0
  · subst a; simp
  by_cases hb : b = 0
  · subst b; simp
  by_cases hc : c = 0
  · subst c; simp
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hnc : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  let a' := (‖a‖⁻¹ : ℂ) • a
  let b' := (‖b‖⁻¹ : ℂ) • b
  let c' := (‖c‖⁻¹ : ℂ) • c
  have ha' : ‖a'‖ ≤ 1 := by simp [a', norm_smul, Complex.norm_real, hna]
  have hb' : ‖b'‖ ≤ 1 := by simp [b', norm_smul, Complex.norm_real, hnb]
  have hc' : ‖c'‖ ≤ 1 := by simp [c', norm_smul, Complex.norm_real, hnc]
  have hu := norm_young_trilinear_unit hp hq ht h a' b' c' ha' hb' hc' S T
  have he : (∑ j ∈ S, ∑ k ∈ T, a j * b k * c (j + k)) =
      ((‖a‖ : ℂ) * (‖b‖ : ℂ) * (‖c‖ : ℂ)) *
        (∑ j ∈ S, ∑ k ∈ T, a' j * b' k * c' (j + k)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    change a j * b k * c (j + k) =
      ((‖a‖ : ℂ) * (‖b‖ : ℂ) * (‖c‖ : ℂ)) *
        (((‖a‖ : ℂ)⁻¹ * a j) * ((‖b‖ : ℂ)⁻¹ * b k) * ((‖c‖ : ℂ)⁻¹ * c (j + k)))
    field_simp [Complex.ofReal_ne_zero.mpr hna, Complex.ofReal_ne_zero.mpr hnb,
      Complex.ofReal_ne_zero.mpr hnc]
  rw [he, norm_mul]
  calc
    _ ≤ ‖(‖a‖ : ℂ) * (‖b‖ : ℂ) * (‖c‖ : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    _ = _ := by simp

end NLS.Coeff
