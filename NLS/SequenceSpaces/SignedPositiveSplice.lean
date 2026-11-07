import NLS.SequenceSpaces.Reflection
import NLS.SequenceSpaces.Multiplier

/-! A bounded linear splice takes the positive modes of one sequence
and reflects the positive modes of another onto the negative tail.
The central coefficient is exactly zero. -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The characteristic symbol of the strictly positive integer frequencies. -/
def positiveFrequencySymbol : Coeff ⊤ :=
  ⟨fun k => if 0 < k then 1 else 0,memℓp_infty ⟨1,by
    rintro _ ⟨k,rfl⟩
    dsimp only
    split_ifs <;> norm_num⟩⟩

/-- Project onto the strictly positive frequencies. -/
def positiveFrequencyProjection : Coeff p →L[ℂ] Coeff p :=
  multiplierCLM positiveFrequencySymbol

@[simp] theorem positiveFrequencyProjection_apply (a : Coeff p) (k : ℤ) :
    positiveFrequencyProjection a k = if 0 < k then a k else 0 := by
  change (if 0 < k then (1 : ℂ) else 0)*a k = _
  split_ifs <;> simp only [one_mul,zero_mul]

/-- Splice two original sequences without changing their positive labels. -/
def signedPositiveSplice : (Coeff p × Coeff p) →L[ℂ] Coeff p :=
  positiveFrequencyProjection.comp (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))+
    reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (positiveFrequencyProjection.comp (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)))

@[simp] theorem signedPositiveSplice_apply (a b : Coeff p) (k : ℤ) :
    signedPositiveSplice (a,b) k =
      (if 0 < k then a k else 0)+(if k < 0 then b (-k) else 0) := by
  change positiveFrequencyProjection a k+positiveFrequencyProjection b (-k) = _
  simp only [positiveFrequencyProjection_apply,neg_pos]

@[simp] theorem signedPositiveSplice_zero (a b : Coeff p) : signedPositiveSplice (a,b) 0 = 0 := by
  simp only [signedPositiveSplice_apply,lt_self_iff_false,ite_false,add_zero]

@[simp] theorem signedPositiveSplice_positive (a b : Coeff p) (k : ℤ) (hk : 0 < k) :
    signedPositiveSplice (a,b) k = a k := by
  simp only [signedPositiveSplice_apply,hk,ite_true,not_lt_of_ge hk.le,ite_false,add_zero]

@[simp] theorem signedPositiveSplice_negative (a b : Coeff p) (k : ℤ) (hk : k < 0) :
    signedPositiveSplice (a,b) k = b (-k) := by
  simp only [signedPositiveSplice_apply,hk,ite_true,not_lt_of_ge hk.le,ite_false,zero_add]

end NLS.Coeff
