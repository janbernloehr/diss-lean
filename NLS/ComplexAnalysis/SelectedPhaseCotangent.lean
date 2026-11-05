import NLS.ComplexAnalysis.ProductPhaseCotangents

/-! Recover a phase cotangent from its two signed coordinate
cotangents, without a branch or square root choice. -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem phaseCotangent_eq_of_signed_pair (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (L M J T : E →L[ℂ] ℂ)
    (hL : L=u • (J-I • T)) (hM : M=v • (J+I • T)) :
    T=(I/2) • (u⁻¹ • L-v⁻¹ • M) := by
  rw [hL,hM,smul_smul,inv_mul_cancel₀ hu,one_smul,smul_smul,inv_mul_cancel₀ hv,one_smul]
  ext h
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul]
  linear_combination (T h)*I_sq

end NLS.ComplexAnalysis
