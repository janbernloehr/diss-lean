import NLS.SequenceSpaces.RealCoeff
import NLS.SequenceSpaces.ExponentEmbedding

/-! # Coefficient-preserving inclusion between real sequence exponents -/
noncomputable section
open scoped ENNReal
namespace NLS.RealCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Include a real sequence into a larger exponent, preserving every coefficient. -/
def exponentInclusion (hpq : p ≤ q) : RealCoeff p →L[ℝ] RealCoeff q :=
  (Coeff.reCLM q).comp (((Coeff.exponentInclusion hpq).restrictScalars ℝ).comp (complexCLM p))

@[simp] theorem exponentInclusion_apply (hpq : p ≤ q) (a : RealCoeff p) (n : ℤ) :
    exponentInclusion hpq a n = a n := by simp [exponentInclusion]

theorem exponentInclusion_injective (hpq : p ≤ q) :
    Function.Injective (exponentInclusion hpq) := by
  intro a b hab
  ext n
  exact congrArg (fun c : RealCoeff q => c n) hab

end NLS.RealCoeff
