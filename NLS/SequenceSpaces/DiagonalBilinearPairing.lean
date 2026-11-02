import NLS.SequenceSpaces.ConjugateDuality
import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.TwoSequenceBound

/-! # Moving bounded diagonal weights across coefficient duality -/
noncomputable section
namespace NLS.Coeff

theorem dualPairing_multiplier_left (s : Coeff ⊤) (a b : Coeff 2) :
    dualPairing (multiplier s a) b = dualPairing a (multiplier s b) := by
  simp only [dualPairing_apply,multiplier_apply]
  apply tsum_congr
  intro j
  ring

theorem norm_le_of_two_sequence_majorant (v a b : Coeff 2) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ j, ‖v j‖ ≤ L*(‖a j‖+‖b j‖)) : ‖v‖ ≤ L*(‖a‖+‖b‖) := by
  have he : ofFunctionOrZero 2 (fun j => v j) = v := by
    ext j
    exact ofFunctionOrZero_apply_of_mem 2 _ (lp.memℓp v) j
  rw [← he]
  exact (memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound _ a b L hL h).2

end NLS.Coeff
