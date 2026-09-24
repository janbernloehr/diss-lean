import NLS.ZakharovShabat.SourceStandardRootOmittedRealGap

/-!
# Signs of normalized standard-root factors on a real gap

The normalizing denominator is positive at nonnegative indices and
negative at negative indices. Combined with the exterior-root sign,
this determines every retained factor's real sign relative to the
selected gap. These statements feed the finite-product parity count.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real normalizing denominator is positive at nonnegative
integer indices, including the exceptional zero mode. -/
theorem singleSpectralDenominator_re_pos_of_nonneg
    (m : ℤ) (hm : 0 ≤ m) : 0 < (singleSpectralDenominator m).re := by
  by_cases hz : m = 0
  · subst m
    simp [singleSpectralDenominator]
  have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
  have hmR : (0:ℝ) < m := by exact_mod_cast hmp
  simpa [singleSpectralDenominator,hz,Complex.mul_re] using
    mul_pos Real.pi_pos hmR

/-- The real normalizing denominator is negative at negative indices. -/
theorem singleSpectralDenominator_re_neg_of_neg
    (m : ℤ) (hm : m < 0) : (singleSpectralDenominator m).re < 0 := by
  have hz : m ≠ 0 := ne_of_lt hm
  have hmR : (m:ℝ) < 0 := by exact_mod_cast hm
  simpa [singleSpectralDenominator,hz,Complex.mul_re] using
    mul_neg_of_pos_of_neg Real.pi_pos hmR

/-- Real numerator and denominator give the expected real quotient. -/
theorem sourceStandardRoot_div_denominator_re
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (x : ℝ)
    (hroot : (sourceStandardRoot hp hp1 ψ m (x:ℂ)).im = 0) :
    (sourceStandardRoot hp hp1 ψ m (x:ℂ) /
      singleSpectralDenominator m).re =
      (sourceStandardRoot hp hp1 ψ m (x:ℂ)).re /
        (singleSpectralDenominator m).re := by
  let w := sourceStandardRoot hp hp1 ψ m (x:ℂ)
  let d := singleSpectralDenominator m
  have hw : w = (w.re:ℂ) := by
    apply Complex.ext
    · rfl
    · exact hroot
  have hd : d = (d.re:ℂ) := by
    apply Complex.ext
    · rfl
    · dsimp [d,singleSpectralDenominator]
      split_ifs <;> simp
  change (w/d).re = w.re/d.re
  rw [hw,hd]
  simp

/-- A normalized factor retained in the omitted product is exactly
the complex embedding of its real part on the selected real gap. -/
theorem sourceStandardRoot_normalized_eq_ofReal_off_selected_realGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {m n : ℤ} (hmn : m ≠ n) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    sourceStandardRoot hp hp1 ψ m (x:ℂ) /
      singleSpectralDenominator m =
      (((sourceStandardRoot hp hp1 ψ m (x:ℂ) /
        singleSpectralDenominator m).re:ℝ):ℂ) := by
  have hr := sourceStandardRoot_im_eq_zero_off_selected_realGap
    hp hp1 ψ hreal hmn hx
  have hd : (singleSpectralDenominator m).im = 0 := by
    unfold singleSpectralDenominator
    split_ifs <;> simp
  apply Complex.ext
  · rfl
  · simp [Complex.div_im,hr,hd]

/-- A negative-index factor before the selected gap is positive
after normalization by its negative denominator. -/
theorem sourceStandardRoot_normalized_re_pos_of_neg_before
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {m n : ℤ} (hmneg : m < 0) (hmn : m < n) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    0 < (sourceStandardRoot hp hp1 ψ m (x:ℂ) /
      singleSpectralDenominator m).re := by
  rw [sourceStandardRoot_div_denominator_re hp hp1 ψ m x
    (sourceStandardRoot_im_eq_zero_off_selected_realGap
      hp hp1 ψ hreal (ne_of_lt hmn) hx)]
  exact div_pos_of_neg_of_neg
    (sourceStandardRoot_re_neg_before_realGap hp hp1 ψ hreal hmn hx)
    (singleSpectralDenominator_re_neg_of_neg m hmneg)

/-- A nonnegative-index factor before the selected gap is negative
after normalization by its positive denominator. -/
theorem sourceStandardRoot_normalized_re_neg_of_nonneg_before
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {m n : ℤ} (hmnonneg : 0 ≤ m) (hmn : m < n) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (sourceStandardRoot hp hp1 ψ m (x:ℂ) /
      singleSpectralDenominator m).re < 0 := by
  rw [sourceStandardRoot_div_denominator_re hp hp1 ψ m x
    (sourceStandardRoot_im_eq_zero_off_selected_realGap
      hp hp1 ψ hreal (ne_of_lt hmn) hx)]
  exact div_neg_of_neg_of_pos
    (sourceStandardRoot_re_neg_before_realGap hp hp1 ψ hreal hmn hx)
    (singleSpectralDenominator_re_pos_of_nonneg m hmnonneg)

/-- A negative-index factor after the selected gap is negative
after normalization by its negative denominator. -/
theorem sourceStandardRoot_normalized_re_neg_of_neg_after
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {m n : ℤ} (hmneg : m < 0) (hnm : n < m) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (sourceStandardRoot hp hp1 ψ m (x:ℂ) /
      singleSpectralDenominator m).re < 0 := by
  rw [sourceStandardRoot_div_denominator_re hp hp1 ψ m x
    (sourceStandardRoot_im_eq_zero_off_selected_realGap
      hp hp1 ψ hreal (Ne.symm (ne_of_lt hnm)) hx)]
  exact div_neg_of_pos_of_neg
    (sourceStandardRoot_re_pos_after_realGap hp hp1 ψ hreal hnm hx)
    (singleSpectralDenominator_re_neg_of_neg m hmneg)

/-- A nonnegative-index factor after the selected gap is positive
after normalization by its positive denominator. -/
theorem sourceStandardRoot_normalized_re_pos_of_nonneg_after
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {m n : ℤ} (hmnonneg : 0 ≤ m) (hnm : n < m) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    0 < (sourceStandardRoot hp hp1 ψ m (x:ℂ) /
      singleSpectralDenominator m).re := by
  rw [sourceStandardRoot_div_denominator_re hp hp1 ψ m x
    (sourceStandardRoot_im_eq_zero_off_selected_realGap
      hp hp1 ψ hreal (Ne.symm (ne_of_lt hnm)) hx)]
  exact div_pos
    (sourceStandardRoot_re_pos_after_realGap hp hp1 ψ hreal hnm hx)
    (singleSpectralDenominator_re_pos_of_nonneg m hmnonneg)

end NLS.ZakharovShabat
