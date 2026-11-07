import NLS.KdV.HillProductEquationDiagonalLimit
import NLS.KdV.HillProductEquationCompactRemainder
import NLS.SequenceSpaces.PositiveDiagonalInverseBound

/-! The actual original real Hill period Jacobian is a diagonal
Banach isomorphism plus its actual compact remainder. The diagonal
inverse and its norm bound retain every original coordinate. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_actual_real_diagonal_equiv (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ m : ℕ+, δ ≤ ‖P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) (lp.single 2 m 1) m‖) ∧
      ∃ D : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
        ∃ K : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
          IsCompactOperator K ∧
          P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) = D.toContinuousLinearMap+K ∧
          (∀ a m, D a m = P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)
            (lp.single 2 m 1) m*a m) ∧
          (∀ a m, D.symm a m =
            (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) (lp.single 2 m 1) m)⁻¹*a m) ∧
          ‖D.symm.toContinuousLinearMap‖ ≤ δ⁻¹ := by
  let T := P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)
  obtain ⟨δ,hδ,hlower,D,hD,hinv⟩ := LpSequence.exists_positiveOperatorDiagonal_equiv_of_tendsto_one T
    (fun m => P.sequenceJacobian_actual_real_diagonal_ne_zero n m q hq hr)
    (P.sequenceJacobian_actual_real_diagonal_tendsto_one q hq hr n)
  refine ⟨δ,hδ,hlower,D,LpSequence.positiveOperatorOffDiagonal T,
    P.sequenceJacobian_actual_real_offDiagonal_compact q hq hr n,?_,?_,hinv,
    LpSequence.norm_positive_diagonal_inverse_le T δ hδ hlower D hinv⟩
  · rw [hD]
    exact LpSequence.positiveOperator_eq_diagonal_add_offDiagonal T
  · intro a m
    change D.toContinuousLinearMap a m = _
    rw [hD]
    exact LpSequence.positiveOperatorDiagonal_apply T a m

end NLS.KdV.HillProductEquationPatch
