import Mathlib.Analysis.Normed.Operator.Basic

/-! A norm comparison for a vector fixed by an operator and a nearby
bounded operator. No orthogonality or finite dimension is assumed. -/
noncomputable section
namespace NLS.FunctionalAnalysis

/-- A nearby operator retains a quantitative part of every fixed vector. -/
theorem norm_image_ge_of_near_fixed {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (P Q : E →L[𝕜] E) (delta : ℝ) (hnear : ‖P-Q‖ ≤ delta) (x : E) (hx : P x=x) :
    (1-delta)*‖x‖ ≤ ‖Q x‖ := by
  have hnorm : ‖x‖ ≤ ‖(P-Q) x‖+‖Q x‖ := by
    calc
      _ = ‖(P-Q) x+Q x‖ := by rw [sub_apply,sub_add_cancel,hx]
      _ ≤ _ := norm_add_le _ _
  have hb := ((P-Q).le_opNorm x).trans (mul_le_mul_of_nonneg_right hnear (norm_nonneg x))
  nlinarith

end NLS.FunctionalAnalysis
