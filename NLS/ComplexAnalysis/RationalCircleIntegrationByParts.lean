import NLS.ComplexAnalysis.CircleIntegralIntegrationByParts

/-! # Integration by parts for a quotient on a circle

Only analyticity near the contour and a nonvanishing denominator there
are required. The circle may enclose poles or spectral branch points.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem circleIntegral_deriv_div_eq (F G : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hF : AnalyticOnNhd ℂ F (sphere c R)) (hG : AnalyticOnNhd ℂ G (sphere c R))
    (hne : ∀ z ∈ sphere c R, G z ≠ 0) :
    (∮ z in C(c,R), deriv F z/G z) = (∮ z in C(c,R), F z*deriv G z/(G z)^2) := by
  have hzero : (∮ z in C(c,R), deriv F z/G z-F z*deriv G z/(G z)^2) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR
    intro z hz
    have hd := (hF z hz).differentiableAt.hasDerivAt.div
      (hG z hz).differentiableAt.hasDerivAt (hne z hz)
    have he : (deriv F z*G z-F z*deriv G z)/(G z)^2 =
        deriv F z/G z-F z*deriv G z/(G z)^2 := by
      field_simp [hne z hz]
    rw [he] at hd
    exact hd.hasDerivWithinAt
  have hi1 : CircleIntegrable (fun z => deriv F z/G z) c R :=
    (hF.deriv.continuousOn.div hG.continuousOn hne).circleIntegrable hR
  have hi2 : CircleIntegrable (fun z => F z*deriv G z/(G z)^2) c R :=
    ((hF.continuousOn.mul hG.deriv.continuousOn).div
      (hG.pow 2).continuousOn (fun z hz => pow_ne_zero 2 (hne z hz))).circleIntegrable hR
  rw [circleIntegral.integral_sub hi1 hi2] at hzero
  exact sub_eq_zero.mp hzero

end NLS.ComplexAnalysis
