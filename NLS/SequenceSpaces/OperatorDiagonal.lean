import NLS.SequenceSpaces.Multiplier

/-!
# Diagonal extraction on full coefficient spaces

The diagonal entries of a bounded operator form a bounded multiplier
symbol. Subtracting that multiplier gives a bounded operator with zero
diagonal and leaves every off-diagonal matrix entry unchanged.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The diagonal matrix entries of a bounded full-space operator. -/
def operatorDiagonalSymbol (T : Coeff p →L[ℂ] Coeff p) : Coeff ⊤ :=
  ⟨fun m => (T (lp.single p m 1)) m, by
    apply memℓp_infty
    refine ⟨‖T‖,?_⟩
    rintro _ ⟨m,rfl⟩
    calc
      ‖(T (lp.single p m 1)) m‖ ≤ ‖T (lp.single p m 1)‖ :=
        lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' _ m
      _ ≤ ‖T‖ * ‖(lp.single p m 1 : Coeff p)‖ := T.le_opNorm _
      _ = ‖T‖ := by simp [lp.norm_single (zero_lt_one.trans_le Fact.out)]⟩

@[simp] theorem operatorDiagonalSymbol_apply
    (T : Coeff p →L[ℂ] Coeff p) (m : ℤ) :
    operatorDiagonalSymbol T m = (T (lp.single p m 1)) m := rfl

/-- Diagonal extraction does not increase the symbol norm. -/
theorem norm_operatorDiagonalSymbol_le (T : Coeff p →L[ℂ] Coeff p) :
    ‖operatorDiagonalSymbol T‖ ≤ ‖T‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg T)
  intro m
  change ‖(T (lp.single p m 1)) m‖ ≤ ‖T‖
  calc
    ‖(T (lp.single p m 1)) m‖ ≤ ‖T (lp.single p m 1)‖ :=
      lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' _ m
    _ ≤ ‖T‖ * ‖(lp.single p m 1 : Coeff p)‖ := T.le_opNorm _
    _ = ‖T‖ := by simp [lp.norm_single (zero_lt_one.trans_le Fact.out)]

/-- The canonical off-diagonal remainder of a bounded operator. -/
def operatorOffDiagonal (T : Coeff p →L[ℂ] Coeff p) :
    Coeff p →L[ℂ] Coeff p := T - multiplierCLM (operatorDiagonalSymbol T)

/-- The diagonal and off-diagonal pieces reconstruct the operator. -/
theorem operator_eq_diagonal_add_offDiagonal
    (T : Coeff p →L[ℂ] Coeff p) :
    T = multiplierCLM (operatorDiagonalSymbol T) + operatorOffDiagonal T := by
  unfold operatorOffDiagonal
  abel

@[simp] theorem operatorOffDiagonal_diagonal
    (T : Coeff p →L[ℂ] Coeff p) (m : ℤ) :
    (operatorOffDiagonal T (lp.single p m 1)) m = 0 := by
  simp [operatorOffDiagonal]

/-- Removing the diagonal preserves every other matrix entry. -/
theorem operatorOffDiagonal_entry_other
    (T : Coeff p →L[ℂ] Coeff p) (m k : ℤ) (hmk : m ≠ k) :
    (operatorOffDiagonal T (lp.single p k 1)) m =
      (T (lp.single p k 1)) m := by
  simp [operatorOffDiagonal,lp.single_apply,hmk]

end NLS.Coeff
