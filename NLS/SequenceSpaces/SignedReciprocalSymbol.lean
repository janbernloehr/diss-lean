import NLS.SequenceSpaces.SignChange
import NLS.SequenceSpaces.DeletedDiagonal
import NLS.SequenceSpaces.Reflection
import NLS.SequenceSpaces.HolderEmbedding

/-! # Actual reciprocal signed symbols from positive-slot data -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Coeff

/-- Physical conjugate reflection of a bounded actual symbol. -/
def symbolConjugation (a : Coeff ⊤) : Coeff ⊤ := star (reflection a)

@[simp] theorem symbolConjugation_apply (a : Coeff ⊤) (n : ℤ) :
    symbolConjugation a n=conj (a (-n)) := by
  simp only [symbolConjugation,lp.star_apply,reflection_apply,starRingEnd_apply]

/-- The actual full signed extension of a zero-extended positive symbol. -/
def completedPositiveSymbol (a : Coeff ⊤) : Coeff ⊤ := a+symbolConjugation a

@[simp] theorem completedPositiveSymbol_apply (a : Coeff ⊤) (n : ℤ) :
    completedPositiveSymbol a n=a n+conj (a (-n)) := by
  simp only [completedPositiveSymbol,lp.coeFn_add,Pi.add_apply,symbolConjugation_apply]

/-- Exact positive reciprocals extend to exact reciprocals at EVERY
nonzero signed index, including the reflected complex phase. -/
theorem completedPositiveSymbol_reciprocal (a b : Coeff ⊤)
    (ha : ∀ n : ℤ, n≤0 → a n=0) (hb : ∀ n : ℤ, n≤0 → b n=0)
    (hab : ∀ n : ℤ, 0<n → a n*b n=1) :
    ∀ n : ℤ, n≠0 → completedPositiveSymbol a n*completedPositiveSymbol b n=1 := by
  intro n hn
  rw [completedPositiveSymbol_apply,completedPositiveSymbol_apply]
  by_cases hp : 0<n
  · rw [ha (-n) (by omega),hb (-n) (by omega),map_zero,add_zero,add_zero]
    exact hab n hp
  · rw [ha n (by omega),hb n (by omega),zero_add,zero_add,←map_mul,hab (-n) (by omega),map_one]

/-- The actual signed extension therefore gives a bounded mean-zero
multiplier equivalence, with the literal reflected reciprocal symbol. -/
def completedPositiveMultiplierEquiv (a b : Coeff ⊤)
    (ha : ∀ n : ℤ, n≤0 → a n=0) (hb : ∀ n : ℤ, n≤0 → b n=0)
    (hab : ∀ n : ℤ, 0<n → a n*b n=1) : DeletedCoeff 2 0 ≃L[ℂ] DeletedCoeff 2 0 :=
  deletedMultiplierEquiv 0 (completedPositiveSymbol a) (completedPositiveSymbol b)
    (completedPositiveSymbol_reciprocal a b ha hb hab)

/-- Literal full symbol multiplication, scalar normalization and fixed signs. -/
def signedProductSymbol (e : ℤ → Bool) (c : ℂ) (a b : Coeff ⊤) : Coeff ⊤ :=
  signChange e (c • holderProduct (q := ⊤) a b)

@[simp] theorem signedProductSymbol_apply (e : ℤ → Bool) (c : ℂ) (a b : Coeff ⊤) (n : ℤ) :
    signedProductSymbol e c a b n=if e n then -(c*(a n*b n)) else c*(a n*b n) := by
  rw [signedProductSymbol,signChange_apply]
  rfl

/-- The SAME fixed signs and actual reciprocal factors cancel exactly. -/
theorem signedProductSymbol_reciprocal (e : ℤ → Bool) (c : ℂ) (hc : c≠0)
    (a b u v : Coeff ⊤) (n : ℤ) (ha : a n*u n=1) (hb : b n*v n=1) :
    signedProductSymbol e c a b n*signedProductSymbol e c⁻¹ u v n=1 := by
  rw [signedProductSymbol_apply,signedProductSymbol_apply]
  have h : (c*(a n*b n))*(c⁻¹*(u n*v n))=(c*c⁻¹)*((a n*u n)*(b n*v n)) := by ring
  cases e n <;> simp only [Bool.false_eq_true,↓reduceIte,mul_neg,neg_mul,neg_neg]
  all_goals rw [h,mul_inv_cancel₀ hc,ha,hb,one_mul,mul_one]

end NLS.Coeff
