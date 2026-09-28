import NLS.SequenceSpaces.DeletedJacobianSymbol
import NLS.SequenceSpaces.CompactTailReciprocalMatrix

/-!
# Compact off-diagonal remainder from retained matrix entries

The canonical diagonal subtraction of a bounded operator has zero
diagonal entries. Reciprocal bounds for its retained off-diagonal
entries on distant rows therefore suffice for compactness. Inputs at
the deleted index and outputs at that index vanish automatically.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A tail reciprocal bound for the retained off-diagonal entries of
a bounded deleted-coordinate operator makes its canonical remainder
compact. No kernel representation or head-row estimate is assumed. -/
theorem isCompactOperator_deletedJacobianOffDiagonal_of_tailEntryBound
    (q : ℝ≥0∞) [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp : p ≠ ⊤) (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (b : Coeff p) (K : ℕ)
    (hoff : ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
      ∀ k : ℤ, ∀ hkn : k ≠ n, k ≠ m →
        ‖((Q (deletedSingleCLM n k hkn 1) :
          DeletedCoeff p n) : Coeff p) m‖ ≤
          ‖b m‖ / |((k-m : ℤ) : ℝ)|) :
    IsCompactOperator (deletedJacobianOffDiagonal n Q) := by
  let T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    deletedJacobianOffDiagonal n Q
  apply isCompactOperator_deleted_of_tailReciprocalMatrixBound
    q hp n T b K
  · intro m hm
    by_cases hmn : m = n
    · subst m
      exact deletedOperatorMatrixEntry_apply_deleted n n T
    · rw [deletedOperatorMatrixEntry_apply_other n m m hmn]
      exact deletedJacobianOffDiagonal_diagonal n m hmn Q
  · intro m hm k hkm
    by_cases hmn : m = n
    · subst m
      have hzero : deletedOperatorMatrixEntry n T n k = 0 :=
        (T (deleteCoordinateTo n (lp.single p k 1))).property
      rw [hzero]
      simp only [norm_zero]
      exact div_nonneg (norm_nonneg (b n))
        (abs_nonneg (((k-n : ℤ) : ℝ)))
    by_cases hkn : k = n
    · subst k
      rw [deletedOperatorMatrixEntry_apply_deleted]
      simp only [norm_zero]
      exact div_nonneg (norm_nonneg (b m))
        (abs_nonneg (((n-m : ℤ) : ℝ)))
    · rw [deletedOperatorMatrixEntry_apply_other n m k hkn,
        deletedJacobianOffDiagonal_entry_other n m k hkn (Ne.symm hkm) Q]
      exact hoff m hm hmn k hkn hkm

end NLS.Coeff
