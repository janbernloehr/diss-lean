import NLS.ComplexAnalysis.InversionCircleCoefficients

/-! The quotient F(z)^2/z has a canonical analytic filling when F(0)=0.
This removes the central pole before contour decomposition. -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

def filledSquareOverZero (F : ℂ → ℂ) (z : ℂ) : ℂ := z*(dslope F 0 z)^2

theorem filledSquareOverZero_zero (F : ℂ → ℂ) : filledSquareOverZero F 0=0 := by
  simp only [filledSquareOverZero,zero_mul]

theorem filledSquareOverZero_eq_div (F : ℂ → ℂ) (hF0 : F 0=0) (z : ℂ) (hz : z ≠ 0) :
    filledSquareOverZero F z=(F z)^2/z := by
  rw [filledSquareOverZero,dslope_of_ne F hz]
  simp only [slope,hF0,vsub_eq_sub,sub_zero,smul_eq_mul]
  field_simp

/-- Analyticity holds on the full original open domain, including zero. -/
theorem analyticOnNhd_filledSquareOverZero (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (h0 : (0:ℂ) ∈ U) (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℂ (filledSquareOverZero F) U := by
  have hd : AnalyticOnNhd ℂ (dslope F 0) U :=
    ((differentiableOn_dslope (hU.mem_nhds h0)).mpr hF.differentiableOn).analyticOnNhd hU
  intro z hz
  exact analyticAt_id.mul ((hd z hz).pow 2)

end NLS.ComplexAnalysis
