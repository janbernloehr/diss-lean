import NLS.RealAnalysis.FourierSquareRootNormalization

/-! Bounds for the half-derivative Fourier symbol between the
inhomogeneous source bracket and the literal signed target bracket. -/
noncomputable section
namespace NLS.RealAnalysis

theorem halfFourier_forward_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ 2*b) : (1/Real.sqrt b)*(1/(c*Real.sqrt b)) ≤ (2/c)*(1/a) := by
  have hs := Real.sqrt_pos.mpr hb
  have hsq := Real.sq_sqrt hb.le
  have he : (1/Real.sqrt b)*(1/(c*Real.sqrt b))=1/(c*b) := by
    rw [one_div_mul_one_div,← mul_assoc,mul_comm (Real.sqrt b) c,mul_assoc,← sq,hsq]
  rw [he,show (2/c)*(1/a)=2/(c*a) by ring]
  apply (div_le_div_iff₀ (mul_pos hc hb) (mul_pos hc ha)).2
  nlinarith

theorem halfFourier_inverse_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hba : b ≤ a) : (1/a)*(c*Real.sqrt b) ≤ c*(1/Real.sqrt b) := by
  have hs := Real.sqrt_pos.mpr hb
  have hsq := Real.sq_sqrt hb.le
  rw [show c*(1/Real.sqrt b)=c/Real.sqrt b by ring]
  apply (le_div_iff₀ hs).2
  calc
    _ = c*b/a := by rw [show 1/a*(c*Real.sqrt b)*Real.sqrt b=c*(Real.sqrt b)^2/a by ring,hsq]
    _ ≤ c := (div_le_iff₀ ha).2 (mul_le_mul_of_nonneg_left hba hc.le)

end NLS.RealAnalysis
