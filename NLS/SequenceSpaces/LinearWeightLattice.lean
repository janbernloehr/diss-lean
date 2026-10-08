import NLS.SequenceSpaces.ReciprocalSeries

/-! # Lattice sums for weights with one linear factor

The estimates retain the zero mode of the bracket weight and remove only the
resonant reciprocal. Combined with the π/2 strip denominator, these constants
suffice for the constant four in Lemma 25.2.
-/
noncomputable section
namespace NLS.ReciprocalSeries

/-- Squared reciprocal of the inhomogeneous integer bracket. -/
def bracketInverseSq (k : ℤ) : ℝ := 1 / (1 + |(k : ℝ)|)^2

/-- Squared reciprocal with the central term zero, using division by zero. -/
def puncturedInverseSq (k : ℤ) : ℝ := 1 / |(k : ℝ)|^2

theorem bracketInverseSq_nonneg (k : ℤ) : 0 ≤ bracketInverseSq k := by
  unfold bracketInverseSq; positivity

theorem puncturedInverseSq_nonneg (k : ℤ) : 0 ≤ puncturedInverseSq k := by
  unfold puncturedInverseSq; positivity

private theorem inv_sq_eq_rpow (x : ℝ) (hx : 0 ≤ x) :
    1 / x^2 = x^(-(2:ℝ)) := by rw [Real.rpow_neg hx, Real.rpow_two, one_div]

theorem summable_bracketInverseSq : Summable bracketInverseSq := by
  have hs := summable_nat_shifted_rpow (by norm_num : (0:ℝ) < 2) (by norm_num : (1:ℝ) < 2)
  have he (k : ℕ) : bracketInverseSq ((k:ℤ)+1) = ((k:ℝ)+2)^(-(2:ℝ)) := by
    unfold bracketInverseSq
    rw [Int.cast_add, Int.cast_natCast, Int.cast_one, abs_of_nonneg (by positivity)]
    rw [show 1+((k:ℝ)+1)=k+2 by ring, inv_sq_eq_rpow _ (by positivity)]
  apply Summable.of_add_one_of_neg_add_one
  · simpa only [he] using hs
  · have hn (k : ℕ) : bracketInverseSq (-((k:ℤ)+1)) = bracketInverseSq ((k:ℤ)+1) := by
      simp only [bracketInverseSq, Int.cast_neg, abs_neg]
    simpa only [hn, he] using hs

theorem summable_puncturedInverseSq : Summable puncturedInverseSq := by
  have h := summable_int_shifted_rpow (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (1:ℝ) < 2)
  convert h using 1
  funext k
  by_cases hk : k = 0
  · simp [hk, puncturedInverseSq]
  · simp [hk, puncturedInverseSq, Real.rpow_neg (abs_nonneg (k:ℝ))]

/-- A rational bound on the full bracket-square sum, including its zero term. -/
theorem tsum_bracketInverseSq_le : (∑' k : ℤ, bracketInverseSq k) ≤ 5/2 := by
  rw [summable_bracketInverseSq.tsum_eq_add_tsum_ite 0]
  have he : (fun k : ℤ => if k = 0 then 0 else bracketInverseSq k) =
      (fun k : ℤ => if k = 0 then 0 else (1+|(k:ℝ)|)^(-(2:ℝ))) := by
    funext k; simp only [bracketInverseSq, inv_sq_eq_rpow (1+|(k:ℝ)|) (by positivity)]
  rw [he, tsum_int_shifted_rpow_eq_two_mul (by norm_num) (by norm_num)]
  have h := tsum_nat_succ_shifted_rpow_le (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 2)
  norm_num [bracketInverseSq, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_two] at h ⊢
  linarith

/-- Removing zero from the homogeneous reciprocal gives a bound of 7/2. -/
theorem tsum_puncturedInverseSq_le : (∑' k : ℤ, puncturedInverseSq k) ≤ 7/2 := by
  have he : puncturedInverseSq =
      (fun k : ℤ => if k = 0 then 0 else (0+|(k:ℝ)|)^(-(2:ℝ))) := by
    funext k
    by_cases hk : k = 0
    · simp [hk, puncturedInverseSq]
    · simp [hk, puncturedInverseSq, Real.rpow_neg (abs_nonneg (k:ℝ))]
  rw [he, tsum_int_shifted_rpow_eq_two_mul (by norm_num) (by norm_num)]
  have hs := summable_nat_shifted_rpow (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ) < 2)
  simp only [zero_add]
  rw [hs.tsum_eq_zero_add]
  have h := tsum_nat_succ_shifted_rpow_le (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 2)
  have he' : (fun b : ℕ => ((↑(b+1):ℝ)+1)^(-(2:ℝ))) =
      (fun b : ℕ => (1+((b:ℝ)+1))^(-(2:ℝ))) := by funext b; push_cast; congr 1; ring
  rw [he']
  norm_num [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_two] at h ⊢
  linarith

/-- The missing resonant term makes the bracket-to-distance ratio at most two. -/
theorem bracket_sq_mul_punctured_le (k : ℤ) :
    (1+|(k:ℝ)|)^2 * puncturedInverseSq k ≤ 4 := by
  by_cases hk : k = 0
  · simp [hk, puncturedInverseSq]
  · have ha : 1 ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
    unfold puncturedInverseSq
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (|(k:ℝ)|-1)]

/-- The two centers ±n force a quadratic gain, uniformly also at n=0. -/
theorem bracket_product_pointwise (n l : ℤ) :
    (1+|(n:ℝ)|)^2 * (bracketInverseSq (l+n) * puncturedInverseSq (l-n)) ≤
      (5/4:ℝ) * (bracketInverseSq (l+n) + puncturedInverseSq (l-n)) := by
  by_cases hl : l = n
  · subst l; simp [puncturedInverseSq, bracketInverseSq]; positivity
  have hb : 1 ≤ |((l-n:ℤ):ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hl)
  have ht : 2*|(n:ℝ)| ≤ |((l+n:ℤ):ℝ)|+|((l-n:ℤ):ℝ)| := by
    have h := abs_sub (l+n:ℝ) (l-n:ℝ)
    norm_num [show (l+n:ℝ)-(l-n)=2*n by ring, abs_mul] at h
    simpa only [Int.cast_add, Int.cast_sub] using h
  have hbound : (1+|(n:ℝ)|)^2 ≤ (5/4:ℝ)*((1+|((l+n:ℤ):ℝ)|)^2+|((l-n:ℤ):ℝ)|^2) := by
    have hlin : 1+|(n:ℝ)| ≤ (1+|((l+n:ℤ):ℝ)|)/2+|((l-n:ℤ):ℝ)| := by linarith
    have hs := sq_le_sq₀ (by positivity : 0 ≤ 1+|(n:ℝ)|) (by positivity : 0 ≤ (1+|((l+n:ℤ):ℝ)|)/2+|((l-n:ℤ):ℝ)|)
    have hsq := hs.mpr hlin
    nlinarith [sq_nonneg ((1+|((l+n:ℤ):ℝ)|)-|((l-n:ℤ):ℝ)|/2)]
  unfold bracketInverseSq puncturedInverseSq
  have ha0 : (1+|((l+n:ℤ):ℝ)|)^2 > 0 := by positivity
  have hb0 : |((l-n:ℤ):ℝ)|^2 > 0 := by positivity
  field_simp
  nlinarith

/-- Summability of the separated-center product. -/
theorem summable_bracket_product (n : ℤ) :
    Summable (fun l : ℤ => bracketInverseSq (l+n) * puncturedInverseSq (l-n)) := by
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (bracketInverseSq_nonneg _) (puncturedInverseSq_nonneg _))
    (fun l => ?_) (summable_puncturedInverseSq.comp_injective (Equiv.subRight n).injective)
  apply mul_le_of_le_one_left (puncturedInverseSq_nonneg _)
  unfold bracketInverseSq
  apply (div_le_one (by positivity)).mpr
  nlinarith [abs_nonneg ((l+n:ℤ):ℝ)]

/-- The mixed reciprocal convolution has uniform quadratic decay. -/
theorem tsum_bracket_product_le (n : ℤ) :
    (∑' l : ℤ, bracketInverseSq (l+n) * puncturedInverseSq (l-n)) ≤
      (15/2:ℝ) / (1+|(n:ℝ)|)^2 := by
  have hA : Summable (fun l : ℤ => bracketInverseSq (l+n)) :=
    summable_bracketInverseSq.comp_injective (Equiv.addRight n).injective
  have hB : Summable (fun l : ℤ => puncturedInverseSq (l-n)) :=
    summable_puncturedInverseSq.comp_injective (Equiv.subRight n).injective
  have h := Summable.tsum_le_tsum (bracket_product_pointwise n)
    ((summable_bracket_product n).mul_left _) ((hA.add hB).mul_left (5/4:ℝ))
  simp only [tsum_mul_left, Summable.tsum_add hA hB] at h
  have heA : (∑' l : ℤ, bracketInverseSq (l+n)) = ∑' l : ℤ, bracketInverseSq l := by
    exact (Equiv.addRight n).tsum_eq bracketInverseSq
  have heB : (∑' l : ℤ, puncturedInverseSq (l-n)) = ∑' l : ℤ, puncturedInverseSq l := by
    simpa only [Equiv.subRight_apply] using (Equiv.subRight n).tsum_eq puncturedInverseSq
  rw [heA, heB] at h
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith [tsum_bracketInverseSq_le, tsum_puncturedInverseSq_le]

end NLS.ReciprocalSeries
