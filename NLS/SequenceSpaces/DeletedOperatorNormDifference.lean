import NLS.SequenceSpaces.DeletedOperatorExtension

/-!
# Norm control of differences of full deleted-Jacobian extensions

The omitted diagonal fill cancels in an operator difference. The full
extension therefore has no larger norm than the deleted block difference.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_deletedJacobianExtension_sub_le
    (n : ℤ) (A B : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    ‖Coeff.deletedJacobianExtension n A-Coeff.deletedJacobianExtension n B‖ ≤ ‖A-B‖ := by
  have he : Coeff.deletedJacobianExtension n A-Coeff.deletedJacobianExtension n B =
      Coeff.deletedOperatorExtension n 0 (A-B) := by
    dsimp only [Coeff.deletedJacobianExtension,Coeff.deletedOperatorExtension]
    simp only [ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub,
      zero_smul,ContinuousLinearMap.comp_zero,add_zero]
    abel
  rw [he]
  simpa only [norm_zero,add_zero] using Coeff.norm_deletedOperatorExtension_le n 0 (A-B)

end NLS.Coeff
