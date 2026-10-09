import NLS.ComplexAnalysis.PolygonalEndpointIntegral

/-! # Two intermediate formula issues in the printed proof of F.2

The shared path occurs in both endpoint integrals and keeps its full
coefficient after averaging. The displayed real majorant on page 134
also fails below the moving threshold. These concern the printed proof,
not the analyticity statement, which is proved by primitive identification.
-/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

/-- Splitting both endpoint paths at the midpoint retains the full common-path term. -/
theorem appendixF_shared_path_normalization (L R J : ℂ) :
    ((-Complex.I*(L+J))+(-Complex.I*(R+J)))/2 =
      -Complex.I*J-Complex.I*(L+R)/2 := by ring

/-- The half coefficient printed in (F.3) differs from the full common-path coefficient. -/
theorem appendixF_half_coefficient_ne (J : ℂ) (hJ : J ≠ 0) :
    -Complex.I*J ≠ (1/(2*Complex.I))*J := by
  intro h
  have hI : (1/(2*Complex.I):ℂ) = -Complex.I/2 := by
    field_simp
    simp
  rw [hI] at h
  have hz : Complex.I*J = 0 := by linear_combination -2*h
  exact (mul_ne_zero Complex.I_ne_zero hJ) hz

/-- The printed proposed real-valued majorant, with real square roots. -/
def appendixFPrintedMajorant (e t : ℝ) : ℝ := Real.sqrt (t+|e|)/Real.sqrt (t-|e|)

/-- Below the threshold the printed denominator is a square root of a negative real.
With Lean's totalized real square root and division, the expression becomes zero. -/
theorem appendixFPrintedMajorant_eq_zero {e t : ℝ} (he : 0 < e) (ht : t < e) :
    appendixFPrintedMajorant e t = 0 := by
  rw [appendixFPrintedMajorant,abs_of_pos he,Real.sqrt_eq_zero_of_nonpos (by linarith : t-e ≤ 0),div_zero]

/-- An imaginary epsilon avoids any real-parameter root singularity, but the
printed majorant still vanishes where the actual normalized quotient is nonzero. -/
theorem appendixF_printed_majorant_counterexample :
    let ε : ℂ := Complex.I/2
    let t : ℝ := 1/4
    let w : ℂ := (Real.sqrt (5/16:ℝ):ℂ)
    0 < t ∧ t < 1 ∧ w^2 = (t:ℂ)^2-ε^2 ∧
      0 < ‖(t:ℂ)/w‖ ∧ appendixFPrintedMajorant ‖ε‖ t = 0 := by
  dsimp only
  have hs : 0 < Real.sqrt (5/16:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨by norm_num,by norm_num,?_,?_,?_⟩
  · rw [← Complex.ofReal_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5/16)]
    norm_num [Complex.ext_iff,pow_two]
  · exact norm_pos_iff.mpr (div_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hs.ne'))
  · have he : ‖(Complex.I/2:ℂ)‖ = (1/2:ℝ) := by norm_num
    rw [he]
    exact appendixFPrintedMajorant_eq_zero (by norm_num) (by norm_num)

end NLS.ComplexAnalysis
