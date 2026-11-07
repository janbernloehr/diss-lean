import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic

/-! Quantitative eigenvalue comparison from an actual projected residual. -/
noncomputable section
namespace NLS.FunctionalAnalysis

/-- A normalized projected residual and the source overlap one half
bound the energy separation, retaining both actual forcing coefficients. -/
theorem norm_separation_of_projected_residual {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : E →L[ℂ] E) (x y v : E) (mu z beta eta gamma nu : ℂ) (C : ℝ)
    (hC : ‖P‖ ≤ C) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hb : ‖beta‖ ≤ 1) (hn : (1/2:ℝ) ≤ ‖nu‖)
    (he : (nu*(mu-z)) • v = (beta*eta) • P x-(beta*gamma) • P y) :
    ‖mu-z‖ ≤ 2*C*(‖eta‖+‖gamma‖) := by
  have hP : 0 ≤ C := (norm_nonneg P).trans hC
  have hpx : ‖P x‖ ≤ C := by
    simpa only [hx,mul_one] using (P.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hC (norm_nonneg x))
  have hpy : ‖P y‖ ≤ C := by
    simpa only [hy,mul_one] using (P.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right hC (norm_nonneg y))
  have ht := norm_sub_le ((beta*eta) • P x) ((beta*gamma) • P y)
  rw [← he,norm_smul,norm_mul,hv,mul_one,norm_smul,norm_smul,norm_mul,norm_mul] at ht
  have hright : ‖beta‖*‖eta‖*‖P x‖+‖beta‖*‖gamma‖*‖P y‖ ≤ C*(‖eta‖+‖gamma‖) := by
    calc
      _ ≤ 1*‖eta‖*C+1*‖gamma‖*C := by gcongr
      _ = _ := by ring
  have hleft := mul_le_mul_of_nonneg_right hn (norm_nonneg (mu-z))
  linarith [ht.trans hright]

end NLS.FunctionalAnalysis
