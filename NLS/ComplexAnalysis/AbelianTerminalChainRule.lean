import NLS.ComplexAnalysis.CosineSegmentGeometry

/-! # Scalar sheet normalization in the Abelian terminal chain rule -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem abelian_terminal_chain (ψ U δ R σ w v : ℂ)
    (hU : U ≠ 0) (hR : R ≠ 0) (hs : σ*(δ*U) = I*R) (hv : (-δ*σ)*w = v) :
    (-I*ψ/U)*w = ψ*v/R := by
  have hroot : R = -I*δ*σ*U := by
    have hI : I*I = -1 := by norm_num
    linear_combination I*hs+R*hI
  apply (eq_div_iff hR).mpr
  rw [hroot,← hv]
  field_simp [hU]
  ring_nf
  simp only [I_sq]
  ring

end NLS.ComplexAnalysis
