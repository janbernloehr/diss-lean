import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.HolderEmbedding

/-! # A summable majorant for diagonal and reciprocal-square entries -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

def reciprocalSquareKernel : Coeff 1 :=
  lp.single 1 0 1 + holderProduct (q := 1)
    (puncturedLattice 2 (by norm_num)) (puncturedLattice 2 (by norm_num))

theorem norm_reciprocalSquareKernel_apply (d : ℤ) :
    ‖reciprocalSquareKernel d‖ = if d = 0 then 1 else (|(d : ℝ)|^2)⁻¹ := by
  by_cases hd : d = 0
  · subst d
    simp [reciprocalSquareKernel,holderProduct_apply]
  simp only [reciprocalSquareKernel,lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,
    if_neg hd,zero_add,holderProduct_apply,puncturedLattice_apply,norm_mul,norm_inv,Complex.norm_intCast]
  simp only [← pow_two,inv_pow]

theorem norm_reciprocalSquareKernel_le : ‖reciprocalSquareKernel‖ ≤ 5 := by
  have hr := norm_puncturedLattice_two_le
  have hn := norm_nonneg (puncturedLattice 2 (by norm_num))
  calc
    _ ≤ ‖(lp.single 1 0 (1 : ℂ) : Coeff 1)‖+
        ‖holderProduct (q := 1) (puncturedLattice 2 (by norm_num)) (puncturedLattice 2 (by norm_num))‖ :=
      norm_add_le _ _
    _ ≤ 1+‖puncturedLattice 2 (by norm_num)‖*‖puncturedLattice 2 (by norm_num)‖ := by
      rw [lp.norm_single (by simp),norm_one]
      exact add_le_add le_rfl (norm_holderProduct_le _ _)
    _ ≤ 5 := by nlinarith

theorem reciprocalSquareKernel_ne_zero (d : ℤ) : reciprocalSquareKernel d ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_reciprocalSquareKernel_apply]
  split_ifs with hd
  · norm_num
  · exact inv_pos.mpr (sq_pos_of_ne_zero (abs_ne_zero.mpr (by exact_mod_cast hd)))

end NLS.Coeff
