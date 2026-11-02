import NLS.SequenceSpaces.Multiplier

/-! # A positive-index weight and its bounded reciprocal

Positive coordinates have their integer weight; the complementary block
has weight one. Only the reciprocal is used as a bounded multiplier.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

def positiveIndexWeight (m : ℤ) : ℂ := if 0 < m then m else 1

theorem one_le_norm_positiveIndexWeight (m : ℤ) : 1 ≤ ‖positiveIndexWeight m‖ := by
  unfold positiveIndexWeight
  split_ifs with hm
  · rw [Complex.norm_intCast,abs_of_pos (by exact_mod_cast hm : (0 : ℝ) < m)]
    exact_mod_cast hm
  · simp only [norm_one,le_refl]

theorem positiveIndexWeight_ne_zero (m : ℤ) : positiveIndexWeight m ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (one_le_norm_positiveIndexWeight m))

def positiveIndexReciprocal : Coeff ⊤ :=
  ⟨fun m => (positiveIndexWeight m)⁻¹,memℓp_infty ⟨1,by
    rintro _ ⟨m,rfl⟩
    change ‖(positiveIndexWeight m)⁻¹‖ ≤ 1
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (one_le_norm_positiveIndexWeight m)⟩⟩

@[simp] theorem positiveIndexReciprocal_apply (m : ℤ) :
    positiveIndexReciprocal m = (positiveIndexWeight m)⁻¹ := rfl

end NLS.Coeff
