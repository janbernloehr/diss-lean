import NLS.SequenceSpaces.DeletedDiagonal
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Diagonal symbol of a bounded deleted-coordinate operator

Evaluating a bounded operator on retained coordinate vectors gives a
uniformly bounded diagonal sequence. Subtracting the corresponding
multiplier leaves an operator with zero diagonal matrix entries.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The diagonal matrix entries of a bounded operator on deleted
`ℓᵖ`, set to zero at the omitted coordinate, form a bounded symbol. -/
def deletedJacobianDiagonalSymbol (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) : Coeff ⊤ :=
  ⟨fun m => if hmn : m = n then 0 else
      ((Q (deletedSingleCLM n m hmn 1) : DeletedCoeff p n) : Coeff p) m,
    by
      apply memℓp_infty
      refine ⟨‖Q‖, ?_⟩
      rintro _ ⟨m,rfl⟩
      by_cases hmn : m = n
      · simp only [dif_pos hmn, norm_zero]
        exact norm_nonneg Q
      · simp only [dif_neg hmn]
        let e : DeletedCoeff p n := deletedSingleCLM n m hmn 1
        have he : ‖e‖ = 1 := by
          change ‖(lp.single p m 1 : Coeff p)‖ = 1
          simp [lp.norm_single (zero_lt_one.trans_le Fact.out)]
        calc
          ‖((Q e : DeletedCoeff p n) : Coeff p) m‖ ≤ ‖Q e‖ :=
            lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' _ m
          _ ≤ ‖Q‖ * ‖e‖ := Q.le_opNorm e
          _ = ‖Q‖ := by rw [he, mul_one]⟩

@[simp] theorem deletedJacobianDiagonalSymbol_apply_same (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    deletedJacobianDiagonalSymbol n Q n = 0 := by
  simp [deletedJacobianDiagonalSymbol]

theorem deletedJacobianDiagonalSymbol_apply_other (n m : ℤ)
    (hmn : m ≠ n) (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    deletedJacobianDiagonalSymbol n Q m =
      ((Q (deletedSingleCLM n m hmn 1) : DeletedCoeff p n) : Coeff p) m := by
  simp [deletedJacobianDiagonalSymbol, hmn]

/-- The symbol is controlled by the norm of the bounded operator. -/
theorem norm_deletedJacobianDiagonalSymbol_le (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    ‖deletedJacobianDiagonalSymbol n Q‖ ≤ ‖Q‖ := by
  apply lp.norm_le_of_forall_le
  · positivity
  intro m
  by_cases hmn : m = n
  · simp only [hmn, deletedJacobianDiagonalSymbol_apply_same, norm_zero]
    exact norm_nonneg Q
  · rw [deletedJacobianDiagonalSymbol_apply_other n m hmn]
    let e : DeletedCoeff p n := deletedSingleCLM n m hmn 1
    have he : ‖e‖ = 1 := by
      change ‖(lp.single p m 1 : Coeff p)‖ = 1
      simp [lp.norm_single (zero_lt_one.trans_le Fact.out)]
    calc
      ‖((Q e : DeletedCoeff p n) : Coeff p) m‖ ≤ ‖Q e‖ :=
        lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' _ m
      _ ≤ ‖Q‖ * ‖e‖ := Q.le_opNorm e
      _ = ‖Q‖ := by rw [he, mul_one]

/-- Subtract the canonical diagonal multiplier from a bounded
deleted-coordinate operator. -/
def deletedJacobianOffDiagonal (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
  Q - deletedMultiplierCLM n (deletedJacobianDiagonalSymbol n Q)

/-- Every bounded deleted-coordinate operator is its extracted
diagonal multiplier plus the off-diagonal remainder. -/
theorem deletedJacobian_eq_diagonal_add_offDiagonal (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    Q = deletedMultiplierCLM n (deletedJacobianDiagonalSymbol n Q) +
      deletedJacobianOffDiagonal n Q := by
  unfold deletedJacobianOffDiagonal
  abel

/-- The off-diagonal remainder vanishes on every diagonal matrix
entry in a retained coordinate. -/
theorem deletedJacobianOffDiagonal_diagonal (n m : ℤ)
    (hmn : m ≠ n) (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    ((deletedJacobianOffDiagonal n Q
      (deletedSingleCLM n m hmn 1) : DeletedCoeff p n) : Coeff p) m = 0 := by
  let e : DeletedCoeff p n := deletedSingleCLM n m hmn 1
  change ((Q e : DeletedCoeff p n) : Coeff p) m -
    ((deletedMultiplierCLM n (deletedJacobianDiagonalSymbol n Q) e :
      DeletedCoeff p n) : Coeff p) m = 0
  rw [deletedMultiplierCLM_apply,
    deletedJacobianDiagonalSymbol_apply_other n m hmn]
  have he : (e : Coeff p) m = 1 := by
    simp [e, deletedSingleCLM_coe]
  rw [he, mul_one, sub_self]

/-- Subtracting the diagonal leaves all off-diagonal matrix entries
unchanged. -/
theorem deletedJacobianOffDiagonal_entry_other (n m k : ℤ)
    (hkn : k ≠ n) (hmk : m ≠ k)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    ((deletedJacobianOffDiagonal n Q
      (deletedSingleCLM n k hkn 1) : DeletedCoeff p n) : Coeff p) m =
      ((Q (deletedSingleCLM n k hkn 1) : DeletedCoeff p n) : Coeff p) m := by
  let e : DeletedCoeff p n := deletedSingleCLM n k hkn 1
  change ((Q e : DeletedCoeff p n) : Coeff p) m -
    ((deletedMultiplierCLM n (deletedJacobianDiagonalSymbol n Q) e :
      DeletedCoeff p n) : Coeff p) m = _
  rw [deletedMultiplierCLM_apply]
  have he : (e : Coeff p) m = 0 := by
    change (lp.single p k (1 : ℂ) : Coeff p) m = 0
    exact lp.single_apply_ne _ _ _ hmk
  rw [he, mul_zero, sub_zero]

end NLS.Coeff
