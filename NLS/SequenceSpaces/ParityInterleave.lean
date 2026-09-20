import NLS.SequenceSpaces.Insertion

/-!
# Interleaving even and odd coefficient sequences

The two isometric insertions assemble independent parity estimates into one
lp sequence on the original signed lattice.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Put the first sequence at even indices and the second at odd indices. -/
def interleave (a b : Coeff p) : Coeff p :=
  insert (parityEmbedding 0) a+insert (parityEmbedding 1) b

/-- The even coefficients retain their original signed indices. -/
theorem interleave_even (a b : Coeff p) (n : ℤ) : interleave a b (2*n) = a n := by
  have he := insert_apply_image (parityEmbedding 0) a n
  have ho := insert_parity_other 1 0 (by norm_num) b n
  simpa [interleave] using congrArg₂ (·+·) he ho

/-- The odd coefficients retain their original signed indices. -/
theorem interleave_odd (a b : Coeff p) (n : ℤ) : interleave a b (2*n+1) = b n := by
  have he := insert_parity_other 0 1 (by norm_num) a n
  have ho := insert_apply_image (parityEmbedding 1) b n
  simpa [interleave] using congrArg₂ (·+·) he ho

/-- The interleaved norm is at most the sum of the two parity norms. -/
theorem norm_interleave_le (a b : Coeff p) : ‖interleave a b‖ ≤ ‖a‖+‖b‖ := by
  simpa only [interleave, norm_insert] using norm_add_le (insert (parityEmbedding 0) a) (insert (parityEmbedding 1) b)

end NLS.Coeff
