import NLS.Dynamics.ComplexBirkhoffCoordinates
import NLS.SequenceSpaces.ExponentEmbedding

/-! # Complex Birkhoff coordinates commute with exponent inclusion -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Birkhoff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The same linear change of coordinates works on every exponent intersection. -/
theorem rectangularToComplex_exponent (hpq : p ≤ q) (z : Coeff p × Coeff p) :
    ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq))
      (rectangularToComplex z) =
    rectangularToComplex
      (((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq)) z) := by
  apply Prod.ext <;> ext n
  · change (rectangularToComplex z).1 n =
      (rectangularToComplex (Coeff.exponentInclusion hpq z.1,
        Coeff.exponentInclusion hpq z.2)).1 n
    simp only [rectangularToComplex_fst,Coeff.exponentInclusion_apply]
  · change (rectangularToComplex z).2 n =
      (rectangularToComplex (Coeff.exponentInclusion hpq z.1,
        Coeff.exponentInclusion hpq z.2)).2 n
    simp only [rectangularToComplex_snd,Coeff.exponentInclusion_apply]
end NLS.Birkhoff
