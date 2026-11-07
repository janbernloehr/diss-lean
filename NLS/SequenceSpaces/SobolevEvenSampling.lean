import NLS.SequenceSpaces.PeriodDoubling
import NLS.SequenceSpaces.HolderEmbedding

/-! Reading even physical Fourier modes preserves exact unit-period Sobolev
weights, with a contractive estimate when the extra order is nonnegative. -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Even physical samples with a nonnegative extra Sobolev weight yield
the exact original unit-period weight, bounded by the full physical norm. -/
theorem exists_sobolev_even_sample_le (a : Coeff p) (f : ℤ → ℂ)
    (t s : ℝ) (hs : 0 ≤ s)
    (ha : ∀ n : ℤ, a (2*n) =
      (Weight.sobolev s (2*n):ℂ)*((Weight.sobolev t n:ℂ)*f n)) :
    ∃ b : Coeff p, (∀ n, b n = (Weight.sobolev (t+s) n:ℂ)*f n) ∧ ‖b‖ ≤ ‖a‖ := by
  have hpoint (n : ℤ) : ‖(Weight.sobolev (t+s) n:ℂ)*f n‖ ≤ ‖periodHalve a n‖ := by
    rw [periodHalve_apply,ha]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev s).positive n),
      abs_of_pos ((Weight.sobolev s).positive (2*n)),
      abs_of_pos ((Weight.sobolev t).positive n),
      Weight.sobolev_add]
    have hw : Weight.sobolev s n ≤ Weight.sobolev s (2*n) := by
      apply Real.rpow_le_rpow (by positivity) _ hs
      simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith [abs_nonneg (n:ℝ)]
    have h := mul_le_mul_of_nonneg_right hw
      (mul_nonneg ((Weight.sobolev t).positive n).le (norm_nonneg (f n)))
    simpa only [mul_assoc,mul_left_comm] using h
  let b : Coeff p := ⟨_,(periodHalve a).property.mono' hpoint⟩
  exact ⟨b,fun _ => rfl,
    (lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hpoint).trans
      (norm_periodHalve_le a)⟩

end NLS.Coeff
