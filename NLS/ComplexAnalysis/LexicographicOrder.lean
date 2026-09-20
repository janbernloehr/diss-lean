import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Prod.Lex

/-!
# Lexicographic order for complex spectral labels

The real part is compared first and the imaginary part breaks ties.
The relation is separate from the standard complex partial order.
-/

noncomputable section
namespace NLS.ComplexAnalysis

/-- Real and imaginary parts as a lexicographically ordered key. -/
def complexLexKey (z : ℂ) : ℝ ×ₗ ℝ := toLex (z.re,z.im)

/-- The source's non-strict lexicographic relation on complex numbers. -/
def complexLexLE (z w : ℂ) : Prop := complexLexKey z ≤ complexLexKey w

theorem complexLexKey_injective : Function.Injective complexLexKey := by
  intro z w h
  have he : (z.re,z.im) = (w.re,w.im) := congrArg ofLex h
  exact Complex.ext (congrArg Prod.fst he) (congrArg Prod.snd he)

instance : IsTrans ℂ complexLexLE := ⟨fun _ _ _ => le_trans⟩
instance : Std.Refl complexLexLE := ⟨fun _ => le_rfl⟩
instance : Std.Total complexLexLE := ⟨fun z w => le_total (complexLexKey z) (complexLexKey w)⟩
instance : Std.Antisymm complexLexLE := ⟨fun _ _ h₁ h₂ => complexLexKey_injective (le_antisymm h₁ h₂)⟩

/-- Lexicographic comparison means strict real comparison or an imaginary comparison at equal real part. -/
theorem complexLexLE_iff (z w : ℂ) :
    complexLexLE z w ↔ z.re < w.re ∨ z.re = w.re ∧ z.im ≤ w.im :=
  Prod.Lex.toLex_le_toLex

/-- Strict separation of real parts fixes lexicographic order. -/
theorem complexLexLE_of_re_lt {z w : ℂ} (h : z.re < w.re) : complexLexLE z w :=
  (complexLexLE_iff z w).mpr (Or.inl h)

/-- Lexicographic order always preserves the order of real parts. -/
theorem re_le_of_complexLexLE {z w : ℂ} (h : complexLexLE z w) : z.re ≤ w.re := by
  rcases (complexLexLE_iff z w).mp h with h | h
  · exact h.le
  · exact h.1.le

/-- On real values the relation is exactly the ordinary real order. -/
theorem complexLexLE_ofReal_iff (a b : ℝ) : complexLexLE (a : ℂ) (b : ℂ) ↔ a ≤ b := by
  rw [complexLexLE_iff]
  simp only [Complex.ofReal_re, Complex.ofReal_im, le_refl, and_true]
  exact le_iff_lt_or_eq.symm

end NLS.ComplexAnalysis
