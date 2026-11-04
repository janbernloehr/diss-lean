import NLS.KdV.HillProductEquationOffDiagonal
import NLS.SequenceSpaces.PositiveKernelCompactness

/-! The off-diagonal remainder of every actual real Hill period
Jacobian is compact. The bounded diagonal has no zero entry; a uniform
positive lower bound, and hence its invertibility, are not asserted. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem sequenceJacobian_actual_real_offDiagonal_compact (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    IsCompactOperator (LpSequence.positiveOperatorOffDiagonal
      (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q))) := by
  obtain ⟨K,hK,hbound⟩ := P.exists_uniform_actual_real_off_diagonal_bound q hq hr
  let T := P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)
  let b : lp (fun _ : ℕ+ => ℂ) 2 := (K:ℂ) • hillHminusGapWidthDisplacement ⟨q,hr⟩
  let κ : ℕ+ → lp (fun _ : ℕ+ => ℂ) 2 := fun m =>
    LpSequence.positiveRestriction (hillFreeInteractionKernel m)
  apply LpSequence.isCompactOperator_positive_of_kernel_entries _ b κ hillFreeInteractionConstant
    hillFreeInteractionConstant_nonneg
    (fun m => (LpSequence.norm_positiveRestriction_le _).trans (norm_hillFreeInteractionKernel_le m))
  intro m r
  rw [LpSequence.positiveOperatorOffDiagonal_entry]
  by_cases hmr : m = r
  · rw [if_pos hmr,norm_zero]
    positivity
  · rw [if_neg hmr]
    have hb : ‖b m‖ = K*‖hillHminusGapWidthDisplacement ⟨q,hr⟩ m‖ := by
      simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hK]
    rw [hb,mul_comm K]
    exact hbound n m r (Ne.symm hmr)

theorem sequenceJacobian_actual_real_diagonal_add_compact (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    ∃ D K : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
      IsCompactOperator K ∧
      P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) = D+K ∧
      (∀ a m, D a m =
        P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) (lp.single 2 m 1) m*a m) ∧
      ∀ m : ℕ+, D (lp.single 2 m 1) m ≠ 0 := by
  let T := P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)
  refine ⟨LpSequence.positiveOperatorDiagonal T,LpSequence.positiveOperatorOffDiagonal T,
    P.sequenceJacobian_actual_real_offDiagonal_compact q hq hr n,
    LpSequence.positiveOperator_eq_diagonal_add_offDiagonal T,
    LpSequence.positiveOperatorDiagonal_apply T,?_⟩
  intro m
  rw [LpSequence.positiveOperatorDiagonal_apply]
  simpa only [lp.single_apply,Pi.single_apply,if_pos,mul_one] using
    P.sequenceJacobian_actual_real_diagonal_ne_zero n m q hq hr

end NLS.KdV.HillProductEquationPatch
