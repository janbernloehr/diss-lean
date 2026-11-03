import NLS.KdV.HillHminusOneBandContinuation
import NLS.KdV.ActionHamiltonianMoments
import NLS.ComplexAnalysis.RealCircleIntegralReflection

/-! # Actual real H^-1 contour periods at every positive gap index

The canonical gap circles lie in the domain of the glued physical
primitive. Their polynomial and shifted cubic integrands are circle
integrable. Exact reflection fixes reality, and integration by parts
identifies the level-zero Arnold period with the literal derivative
integral. Complex-potential analytic extension and matching to the
existing common high family remain separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV

def hillHminusRealGapContourMoment (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (m : ℕ) : ℂ :=
  -(Real.pi : ℂ)⁻¹ * ∮ z in C((hillHminusRealGapCenter q hr (n : ℕ) : ℂ),
    hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)),
      z^m*hillHminusRealCutPrimitive q z

def hillHminusRealGapCubicContourMoment (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∮ z in C((hillHminusRealGapCenter q hr (n : ℕ) : ℂ),
    hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)),
      (hillHminusRealCutPrimitive q z+I*(n : ℂ)*Real.pi)^3

theorem hillHminusRealGapContourRadius_pos (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    0 < hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ) := by
  obtain ⟨hd,hη,_,_,_⟩ := hillHminusRealGapContour_geometry q hr (n : ℕ) n.property
  linarith

theorem circleIntegrable_hillHminusRealGapContourIntegrand (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (m : ℕ) :
    CircleIntegrable (fun z => z^m*hillHminusRealCutPrimitive q z)
      (hillHminusRealGapCenter q hr (n : ℕ) : ℂ)
      (hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)) := by
  apply ContinuousOn.circleIntegrable (hillHminusRealGapContourRadius_pos q hr n).le
  exact (continuousOn_id.pow m).mul
    ((analyticOnNhd_hillHminusRealCutPrimitive q hr).mono
      (hillHminusRealGapContour_sphere_subset q hr (n : ℕ) n.property)).continuousOn

theorem circleIntegrable_hillHminusRealGapCubicIntegrand (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    CircleIntegrable (fun z => (hillHminusRealCutPrimitive q z+I*(n : ℂ)*Real.pi)^3)
      (hillHminusRealGapCenter q hr (n : ℕ) : ℂ)
      (hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)) := by
  apply ContinuousOn.circleIntegrable (hillHminusRealGapContourRadius_pos q hr n).le
  exact (((analyticOnNhd_hillHminusRealCutPrimitive q hr).mono
    (hillHminusRealGapContour_sphere_subset q hr (n : ℕ) n.property)).continuousOn.add
      continuousOn_const).pow 3

theorem hillHminusRealGapContourMoment_im_eq_zero (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (m : ℕ) :
    (hillHminusRealGapContourMoment q hr n m).im = 0 := by
  have hi := circleIntegral_im_eq_zero_of_anti_conj
    (fun z => z^m*hillHminusRealCutPrimitive q z) (hillHminusRealGapCenter q hr (n : ℕ))
    (hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ))
    (hillHminusRealGapContourRadius_pos q hr n) (by
      intro z hz
      rw [hillHminusRealCutPrimitive_conj q hr z
        (hillHminusRealGapContour_sphere_subset q hr (n : ℕ) n.property hz),map_mul,map_pow]
      ring)
  simp only [hillHminusRealGapContourMoment,← ofReal_inv,← ofReal_neg,mul_im,ofReal_re,ofReal_im,
    hi,mul_zero,zero_mul,add_zero]

theorem hillHminusRealGapCubicContourMoment_im_eq_zero (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (hillHminusRealGapCubicContourMoment q hr n).im = 0 := by
  have hi := circleIntegral_im_eq_zero_of_anti_conj
    (fun z => (hillHminusRealCutPrimitive q z+I*(n : ℂ)*Real.pi)^3)
    (hillHminusRealGapCenter q hr (n : ℕ))
    (hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ))
    (hillHminusRealGapContourRadius_pos q hr n) (by
      intro z hz
      rw [hillHminusRealCutPrimitive_conj q hr z
        (hillHminusRealGapContour_sphere_subset q hr (n : ℕ) n.property hz),
        map_pow,map_add,map_mul,map_mul,map_natCast,conj_ofReal,conj_I]
      ring)
  simp only [hillHminusRealGapCubicContourMoment,← ofReal_inv,mul_im,ofReal_re,ofReal_im,
    hi,mul_zero,zero_mul,add_zero]

/-- The derivative form has the exact Arnold normalization 1/pi;
there is no additional factor i. -/
theorem hillHminusRealGapContourMoment_zero_eq_derivative_period
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusRealGapContourMoment q hr n 0 =
      (Real.pi : ℂ)⁻¹ * ∮ z in C((hillHminusRealGapCenter q hr (n : ℕ) : ℂ),
        hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)),
          z*(deriv (hillHminusDiscriminant q) z/hillHminusRealCutRoot q z) := by
  simp only [hillHminusRealGapContourMoment,pow_zero,one_mul]
  change primitiveAction (hillHminusRealCutPrimitive q)
    (hillHminusRealGapCenter q hr (n : ℕ) : ℂ)
    (hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)) = _
  rw [primitiveAction_eq_derivative_period (hillHminusRealCutPrimitive q)
    (hillHminusRealCutDomain q hr) (analyticOnNhd_hillHminusRealCutPrimitive q hr)
    _ _ (hillHminusRealGapContourRadius_pos q hr n).le
    (hillHminusRealGapContour_sphere_subset q hr (n : ℕ) n.property)]
  congr 1
  apply circleIntegral.integral_congr (hillHminusRealGapContourRadius_pos q hr n).le
  intro z hz
  change z*deriv (hillHminusRealCutPrimitive q) z = _
  rw [(hasDerivAt_hillHminusRealCutPrimitive q hr z
    (hillHminusRealGapContour_sphere_subset q hr (n : ℕ) n.property hz)).deriv]

end NLS.KdV
