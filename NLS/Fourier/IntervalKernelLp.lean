import NLS.Fourier.IntervalKernel
import NLS.SequenceSpaces.SobolevEmbedding

/-!
# Summability and the endpoint obstruction for the interval kernel

The reciprocal odd tail belongs to every `ℓp` with `p > 1`, including `∞`,
but not to `ℓ1`. This establishes membership for finite Fourier input;
it does not assert a uniform operator bound in the input `ℓp` norm.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Fourier

theorem overlap_shift (k n : ℤ) : overlap k n = overlap 0 (n - 2 * k) := by
  simp only [overlap_eq_unitIntegral]
  congr 2
  ring

/-- The absolute size of the odd kernel coefficients. -/
theorem norm_overlap_zero_odd (l : ℤ) :
    ‖overlap 0 (2 * l + 1)‖ = 1 / (Real.pi * |((2 * l + 1 : ℤ) : ℝ)|) := by
  rw [overlap_odd]
  have he : (2 * (0 : ℂ) - 2 * l - 1) = -((2 * l + 1 : ℤ) : ℂ) := by
    push_cast
    ring
  simp only [Int.cast_zero]
  rw [he]
  rw [norm_div, norm_I, norm_mul, norm_neg, ← Complex.ofReal_intCast,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]

/-- A summable-power envelope for the normalized half-period kernel. -/
theorem norm_overlap_zero_le (n : ℤ) :
    ‖overlap 0 n‖ ≤ 2 * (1 + |(n : ℝ)|)⁻¹ := by
  obtain ⟨l, rfl | rfl⟩ : ∃ l : ℤ, n = 2 * l ∨ n = 2 * l + 1 := ⟨n / 2, by omega⟩
  · rw [overlap_even]
    by_cases hl : l = 0
    · subst l
      norm_num
    · simp only [if_neg (Ne.symm hl), norm_zero]
      positivity
  · rw [norm_overlap_zero_odd]
    have habs : 1 ≤ |((2 * l + 1 : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (by omega : 2 * l + 1 ≠ 0)
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [Real.two_le_pi]

/-- Each translated interval kernel is an actual `ℓp` sequence for `p > 1`. -/
theorem overlap_zero_memlp {p : ℝ≥0∞} (hp : 1 < p) : Memℓp (overlap 0) p := by
  apply ((Weight.inverse_sobolev_one_memlp hp).norm.const_mul (2 : ℝ)).mono
  intro n
  simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs, Weight.sobolev_apply,
    Real.rpow_one, abs_of_pos (by positivity : 0 < 1 + |(n : ℝ)|)] using norm_overlap_zero_le n

/-- The one-sided constant's reciprocal tail rules out an `ℓ1` interval extension. -/
theorem not_memlp_overlap_zero_one : ¬Memℓp (overlap 0) 1 := by
  intro h
  have hs := h.norm.summable_of_one.comp_injective
    (show Function.Injective (fun n : ℕ => (2 * (n : ℤ) + 1)) by intro m n h; dsimp at h; omega)
  have ht : Summable (fun n : ℕ => 1 / (Real.pi * (2 * (n : ℝ) + 1))) := by
    apply hs.congr
    intro n
    simp only [Function.comp_def, norm_overlap_zero_odd, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat, Int.cast_natCast, Int.cast_one]
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (n : ℝ) + 1)]
  have hh : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ (ht.mul_left (2 * Real.pi))
    intro n
    have he : 2 * Real.pi * (1 / (Real.pi * (2 * (n : ℝ) + 1))) = 2 / (2 * n + 1) := by
      field_simp
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp (by simpa using hh))

end NLS.Fourier
