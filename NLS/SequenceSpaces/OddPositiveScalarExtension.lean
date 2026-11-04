import NLS.SequenceSpaces.SymmetricPositiveCutoff

/-! The literal odd extension of positive scalar samples retains
its central zero and exact reflected values. -/
noncomputable section
open Set
namespace NLS.LpSequence

def oddPositiveScalarExtension (u : ℕ+ → ℂ) (j : ℤ) : ℂ :=
  positiveScalarExtension u j-positiveScalarExtension u (-j)

theorem oddPositiveScalarExtension_neg (u : ℕ+ → ℂ) (j : ℤ) :
    oddPositiveScalarExtension u (-j) = -oddPositiveScalarExtension u j := by
  simp only [oddPositiveScalarExtension,neg_neg,neg_sub]

theorem oddPositiveScalarExtension_zero (u : ℕ+ → ℂ) : oddPositiveScalarExtension u 0=0 := by
  simp only [oddPositiveScalarExtension,neg_zero,sub_self]

theorem oddPositiveScalarExtension_apply (u : ℕ+ → ℂ) (m : ℕ+) :
    oddPositiveScalarExtension u ((m:ℕ):ℤ)=u m := by
  rw [oddPositiveScalarExtension,positiveScalarExtension_apply,
    positiveScalarExtension_eq_zero_of_nonpos _ _ (by have := m.pos; omega),sub_zero]

end NLS.LpSequence
