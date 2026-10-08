import NLS.SequenceSpaces.LinearWeightLattice
import NLS.ZakharovShabat.ComplementaryStrip

/-! # The Hilbert kernel behind Lemma 25.2

Retaining the factor π/2 in the strip denominator gives a uniform squared
kernel bound of 16/⟨n⟩², including the zero strip and its lattice center.
-/
noncomputable section
open NLS.ReciprocalSeries
namespace NLS.ZakharovShabat

/-- The closed strip retains a factor π/2 beyond the integer distance. -/
theorem resonantStrip_denominator_lower_pi {n m : ℤ} {z : ℂ}
    (hz : z ∈ resonantStrip n) (hm : m ≠ n) :
    Real.pi/2 * |((m-n:ℤ):ℝ)| ≤ ‖z-(Real.pi:ℂ)*m‖ := by
  have ha : 1 ≤ |((m-n:ℤ):ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hm)
  have ht : Real.pi*|((m-n:ℤ):ℝ)| ≤ |z.re-Real.pi*m|+|z.re-Real.pi*n| := by
    have h := norm_sub_le (z.re-Real.pi*m) (z.re-Real.pi*n)
    have he : (z.re-Real.pi*m)-(z.re-Real.pi*n) = -Real.pi*((m-n:ℤ):ℝ) := by push_cast; ring
    simpa only [he, norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos Real.pi_pos] using h
  have hr : |z.re-Real.pi*m| ≤ ‖z-(Real.pi:ℂ)*m‖ := by
    simpa using Complex.abs_re_le_norm (z-(Real.pi:ℂ)*m)
  change |z.re-Real.pi*n| ≤ Real.pi/2 at hz
  nlinarith [Real.pi_pos]

/-- A rational squared majorant, with no separate exception at resonance. -/
theorem norm_complementarySymbol_sq_le {n : ℤ} {z : ℂ}
    (hz : z ∈ resonantStrip n) (k : ℤ) :
    ‖complementarySymbol n z k‖^2 ≤ (4/9:ℝ)*puncturedInverseSq (k-n) := by
  by_cases hk : k = n
  · simp [hk, puncturedInverseSq]
  have h := resonantStrip_denominator_lower_pi hz hk
  have ha : 1 ≤ |((k-n:ℤ):ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hk)
  have hd : 0 < ‖z-(Real.pi:ℂ)*k‖ := lt_of_lt_of_le zero_lt_one (resonantStrip_denominator_one_le hz hk)
  have hden : (3/2:ℝ)*|((k-n:ℤ):ℝ)| ≤ ‖z-(Real.pi:ℂ)*k‖ := by
    nlinarith [Real.pi_gt_three]
  simp only [complementarySymbol, if_neg hk, norm_inv, puncturedInverseSq]
  rw [inv_pow, inv_eq_one_div, mul_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) (by positivity)).mpr
  nlinarith [sq_nonneg (‖z-(Real.pi:ℂ)*k‖-(3/2:ℝ)*|((k-n:ℤ):ℝ)|)]

/-- Weight ratio times the two actual complementary free denominators. -/
def linearWeightKernel (n : ℤ) (z : ℂ) (k l : ℤ) : ℝ :=
  (1+|((k-n:ℤ):ℝ)|) / ((1+|((k+l:ℤ):ℝ)|)*(1+|((l+n:ℤ):ℝ)|)) *
    ‖complementarySymbol n z k‖ * ‖complementarySymbol n z l‖

theorem linearWeightKernel_nonneg (n : ℤ) (z : ℂ) (k l : ℤ) :
    0 ≤ linearWeightKernel n z k l := by unfold linearWeightKernel; positivity

/-- A summable majorant on the entire double lattice. -/
theorem linearWeightKernel_sq_le {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) (k l : ℤ) :
    linearWeightKernel n z k l ^ 2 ≤ (64/81:ℝ)*bracketInverseSq (k+l)*
      (bracketInverseSq (l+n)*puncturedInverseSq (l-n)) := by
  have hk := norm_complementarySymbol_sq_le hz k
  have hl := norm_complementarySymbol_sq_le hz l
  have hratio := bracket_sq_mul_punctured_le (k-n)
  have hA := bracketInverseSq_nonneg (k+l)
  have hB := bracketInverseSq_nonneg (l+n)
  have hP := puncturedInverseSq_nonneg (k-n)
  calc
    _ = (1+|((k-n:ℤ):ℝ)|)^2*bracketInverseSq (k+l)*bracketInverseSq (l+n)*
        (‖complementarySymbol n z k‖^2*‖complementarySymbol n z l‖^2) := by
      unfold linearWeightKernel bracketInverseSq
      simp only [mul_pow, div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    _ ≤ (1+|((k-n:ℤ):ℝ)|)^2*bracketInverseSq (k+l)*bracketInverseSq (l+n)*
        (((4/9:ℝ)*puncturedInverseSq (k-n))*((4/9:ℝ)*puncturedInverseSq (l-n))) := by
      gcongr
    _ = ((1+|((k-n:ℤ):ℝ)|)^2*puncturedInverseSq (k-n))*
        ((16/81:ℝ)*bracketInverseSq (k+l)*(bracketInverseSq (l+n)*puncturedInverseSq (l-n))) := by ring
    _ ≤ 4*((16/81:ℝ)*bracketInverseSq (k+l)*(bracketInverseSq (l+n)*puncturedInverseSq (l-n))) := by
      exact mul_le_mul_of_nonneg_right hratio (by
        have := bracketInverseSq_nonneg (k+l)
        have := bracketInverseSq_nonneg (l+n)
        have := puncturedInverseSq_nonneg (l-n)
        positivity)
    _ = _ := by ring

private theorem summable_kernel_majorant (n : ℤ) :
    Summable (fun p : ℤ × ℤ => (64/81:ℝ)*bracketInverseSq (p.2+p.1)*
      (bracketInverseSq (p.1+n)*puncturedInverseSq (p.1-n))) := by
  apply (summable_prod_of_nonneg (f := fun p : ℤ × ℤ => (64/81:ℝ)*bracketInverseSq (p.2+p.1)*
      (bracketInverseSq (p.1+n)*puncturedInverseSq (p.1-n))) (by
    intro p
    exact mul_nonneg (mul_nonneg (by norm_num) (bracketInverseSq_nonneg _))
      (mul_nonneg (bracketInverseSq_nonneg _) (puncturedInverseSq_nonneg _)))).mpr
  constructor
  · intro l
    have hs : Summable (fun k : ℤ => bracketInverseSq (k+l)) :=
      summable_bracketInverseSq.comp_injective (Equiv.addRight l).injective
    exact (hs.mul_left (64/81:ℝ)).mul_right (bracketInverseSq (l+n)*puncturedInverseSq (l-n))
  · have he (l : ℤ) : (∑' k : ℤ, (64/81:ℝ)*bracketInverseSq (k+l)*
        (bracketInverseSq (l+n)*puncturedInverseSq (l-n))) =
        ((64/81:ℝ)*(∑' k : ℤ, bracketInverseSq k))*(bracketInverseSq (l+n)*puncturedInverseSq (l-n)) := by
      rw [tsum_mul_right, tsum_mul_left]
      congr 2
      exact (Equiv.addRight l).tsum_eq bracketInverseSq
    simp only [he]
    exact (summable_bracket_product n).mul_left _

/-- The actual double kernel is square summable, not merely formally summable. -/
theorem summable_linearWeightKernel_sq {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) :
    Summable (fun p : ℤ × ℤ => linearWeightKernel n z p.2 p.1 ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun p => linearWeightKernel_sq_le hz p.2 p.1)
    (summable_kernel_majorant n)

/-- The squared Hilbert kernel bound needed for the constant four in Lemma 25.2. -/
theorem tsum_linearWeightKernel_sq_le {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) :
    (∑' p : ℤ × ℤ, linearWeightKernel n z p.2 p.1 ^ 2) ≤ 16/(1+|(n:ℝ)|)^2 := by
  have h := Summable.tsum_le_tsum (fun p : ℤ × ℤ => linearWeightKernel_sq_le hz p.2 p.1)
    (summable_linearWeightKernel_sq hz) (summable_kernel_majorant n)
  rw [(summable_kernel_majorant n).tsum_prod] at h
  have he (l : ℤ) : (∑' k : ℤ, (64/81:ℝ)*bracketInverseSq (k+l)*
        (bracketInverseSq (l+n)*puncturedInverseSq (l-n))) =
        ((64/81:ℝ)*(∑' k : ℤ, bracketInverseSq k))*(bracketInverseSq (l+n)*puncturedInverseSq (l-n)) := by
    rw [tsum_mul_right, tsum_mul_left]
    congr 2
    exact (Equiv.addRight l).tsum_eq bracketInverseSq
  simp only [he, tsum_mul_left] at h
  apply h.trans
  calc
    _ ≤ ((64/81:ℝ)*(5/2))*((15/2:ℝ)/(1+|(n:ℝ)|)^2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left tsum_bracketInverseSq_le (by norm_num)
      · exact tsum_bracket_product_le n
      · exact tsum_nonneg (fun l => mul_nonneg (bracketInverseSq_nonneg _) (puncturedInverseSq_nonneg _))
      · norm_num
    _ ≤ _ := by
      have hp : 0 < (1+|(n:ℝ)|)^2 := by positivity
      apply (le_div_iff₀ hp).mpr
      field_simp
      norm_num

end NLS.ZakharovShabat
