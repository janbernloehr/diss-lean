import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module

/-! The constant complex-linear change from a two-component first-order
system to its sum and difference coordinates. -/
noncomputable section
open Complex
namespace NLS
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

def complexPairRotationCLM : (E × E) →L[ℂ] E × E :=
  ((ContinuousLinearMap.fst ℂ E E)+I • (ContinuousLinearMap.snd ℂ E E)).prod
    ((ContinuousLinearMap.fst ℂ E E)-I • (ContinuousLinearMap.snd ℂ E E))

def complexPairRotationInverseCLM : (E × E) →L[ℂ] E × E :=
  ((1/2:ℂ) • ((ContinuousLinearMap.fst ℂ E E)+(ContinuousLinearMap.snd ℂ E E))).prod
    ((-I/2:ℂ) • ((ContinuousLinearMap.fst ℂ E E)-(ContinuousLinearMap.snd ℂ E E)))

theorem complexPairRotation_leftInverse :
    Function.LeftInverse (complexPairRotationInverseCLM E) (complexPairRotationCLM E) := by
  rintro ⟨a,b⟩
  change ((1/2:ℂ) • ((a+I • b)+(a-I • b)),(-I/2:ℂ) • ((a+I • b)-(a-I • b))) = (a,b)
  apply Prod.ext
  · module
  · have he : (a+I • b)-(a-I • b) = (2*I) • b := by module
    rw [he,smul_smul]
    have hc : (-I/2)*(2*I) = (1:ℂ) := by ring_nf; norm_num [I_sq]
    rw [hc,one_smul]

theorem complexPairRotation_rightInverse :
    Function.RightInverse (complexPairRotationInverseCLM E) (complexPairRotationCLM E) := by
  rintro ⟨a,b⟩
  have hc : I*(-I/2) = (1/2:ℂ) := by ring_nf; norm_num [I_sq]
  change ((1/2:ℂ) • (a+b)+I • ((-I/2:ℂ) • (a-b)),
    (1/2:ℂ) • (a+b)-I • ((-I/2:ℂ) • (a-b))) = (a,b)
  simp only [smul_smul,hc]
  apply Prod.ext <;> module

/-- The exact bounded linear change (a,b) ↦ (a+i*b,a-i*b), with explicit inverse. -/
def complexPairRotation : (E × E) ≃L[ℂ] E × E where
  toLinearEquiv :=
    { toFun := complexPairRotationCLM E
      invFun := complexPairRotationInverseCLM E
      left_inv := complexPairRotation_leftInverse E
      right_inv := complexPairRotation_rightInverse E
      map_add' := (complexPairRotationCLM E).map_add
      map_smul' := (complexPairRotationCLM E).map_smul }
  continuous_toFun := (complexPairRotationCLM E).continuous
  continuous_invFun := (complexPairRotationInverseCLM E).continuous

theorem complexPairRotation_apply (a b : E) :
    complexPairRotation E (a,b) = (a+I • b,a-I • b) := rfl

theorem complexPairRotation_symm_apply (a b : E) :
    (complexPairRotation E).symm (a,b) = ((1/2:ℂ) • (a+b),(-I/2:ℂ) • (a-b)) := rfl

end NLS
