import NLS.KdV.HillHminusOriginalActions
import NLS.KdV.HillHminusOriginalGapPairs
import NLS.KdV.HillHminusOneUniformActionRatios

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory NLS.ComplexAnalysis
namespace NLS.KdV

/-- The actual local high action, defined analytically without gap division. -/
def hillHminusLocalHighAction (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (a : PeriodOneHminusOne) : ℂ :=
  hillHminusSquaredHalfGap n r a/(2*((Real.pi : ℂ)*(n : ℕ)))*hillHminusNormalizedActionRatio n r K a

theorem analyticOnNhd_hillHminusLocalHighAction
    (n : ℕ+) (r : ℝ) (hr : 0<r) (V : Set PeriodOneHminusOne) (hV : IsOpen V)
    (K : ℂ × PeriodOneHminusOne → ℂ)
    (hJ : AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V))
    (hpairs : ∀ a∈V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u) :
    AnalyticOnNhd ℂ (hillHminusLocalHighAction n r K) V := by
  have hg := (analyticOnNhd_hillHminus_symmetric_gap_data n r hr V hV hpairs).2
  have hR := analyticOnNhd_hillHminusNormalizedActionRatio n r hr V hV K hJ hpairs
  intro a ha
  change AnalyticAt ℂ (fun b => hillHminusSquaredHalfGap n r b/(2*((Real.pi : ℂ)*(n : ℕ)))*
    hillHminusNormalizedActionRatio n r K b) a
  exact (hg a ha).div_const.mul (hR a ha)

/-- Exact boundary integral normalization of the analytic local action. -/
theorem hillHminusLocalHighAction_eq_boundary
    (n : ℕ+) (r epsilon : ℝ) (hr : 0<r) (hepsilon : epsilon<1)
    (V : Set PeriodOneHminusOne) (K : ℂ × PeriodOneHminusOne → ℂ)
    (hJ : AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V))
    (a : PeriodOneHminusOne) (ha : a∈V) (l u : ℝ) (hlu : l≤u)
    (hpair : HillHminusHighGapPair a n r (l : ℂ) (u : ℂ))
    (hf : ∀ z∈ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,a)=-hillHminusGapPolynomial n r (z,a)*hillHminusJointNormalizedGapRoot n r K (z,a)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (hnorm : ∀ z∈ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,a)-1‖≤epsilon) :
    hillHminusLocalHighAction n r K a=hillHminusGapBoundaryAction K a l u := by
  have hA := (hillHminusGapBoundaryAction_properties n r epsilon hr hepsilon V K hJ a ha l u hlu hpair hf hnorm).2.1
  have hmean : (fun t : ℝ => hillHminusJointNormalizedGapRoot n r K
      ((((l+u)/2+(u-l)/2*t : ℝ) : ℂ),a))=
      (fun t : ℝ => hillHminusJointNormalizedGapRoot n r K
        (((l : ℂ)+(u : ℂ))/2+((u : ℂ)-(l : ℂ))/2*(t : ℂ),a)) := by
    funext t
    congr 1
    push_cast
    rfl
  rw [hmean,←hillHminusNormalizedActionRatio_eq_mean n r hr K a (l : ℂ) (u : ℂ) hpair] at hA
  rw [hA,hillHminusLocalHighAction,(hpair.symmetric_gap_data hr).2]
  congr 1
  push_cast
  field_simp
  ring

end NLS.KdV
