import NLS.KdV.HillHminusOneGapBoundary
import NLS.ComplexAnalysis.RealGapIntegralNormalization

/-! # The actual Hill gap-boundary integral and its normalization

This is the integral of the PROVED upper primitive boundary value, with
the factor two over pi. It has the exact quadratic-gap normalization,
including a collapsed gap. Identification with the original contour
action is a separate remaining obligation.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusGapBoundaryAction (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℝ) : ℂ :=
  (2/(Real.pi : ℂ)) * ∫ x in l..u, Complex.sqrt (K ((x : ℂ),q))

theorem hillHminusGapBoundaryAction_properties
    (n : ℕ+) (r epsilon : ℝ) (hr : 0 < r) (hepsilon : epsilon < 1)
    (V : Set PeriodOneHminusOne) (K : ℂ × PeriodOneHminusOne → ℂ)
    (hJ : AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V))
    (q : PeriodOneHminusOne) (hqV : q ∈ V) (l u : ℝ) (hlu : l ≤ u)
    (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (hnorm : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,q)-1‖ ≤ epsilon) :
    IntervalIntegrable (fun x : ℝ => Complex.sqrt (K ((x : ℂ),q))) volume l u ∧
    hillHminusGapBoundaryAction K q l u =
      (((u-l : ℝ) : ℂ)^2/(8*((Real.pi : ℂ)*(n : ℕ)))) *
        normalizedSemicircleMean (fun t : ℝ => hillHminusJointNormalizedGapRoot n r K
          ((((l+u)/2+(u-l)/2*t : ℝ) : ℂ),q)) ∧
    ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusGapBoundaryAction K q l u-
      (((u-l : ℝ) : ℂ)^2)‖ ≤ (u-l)^2*epsilon := by
  let S : ℝ → ℂ := fun x => hillHminusJointNormalizedGapRoot n r K ((x : ℂ),q)
  have hS : ContinuousOn S (Icc l u) := by
    intro x hx
    exact ((hJ ((x : ℂ),q) ⟨hpair.real_gap_mem_ball x hx,hqV⟩).continuousAt.comp
      (f := fun x : ℝ => ((x : ℂ),q)) (by fun_prop)).continuousWithinAt
  have hv (x : ℝ) (hx : x ∈ Icc l u) : Complex.sqrt (K ((x : ℂ),q)) =
      (((Real.sqrt ((x-l)*(u-x))/(2*(Real.pi*(n : ℕ))) : ℝ) : ℂ))*S x :=
    hillHminus_real_gap_sqrt_value n r epsilon hr hepsilon K q l u hpair hf hnorm x hx
  have hi : ContinuousOn (fun x : ℝ => Complex.sqrt (K ((x : ℂ),q))) (Icc l u) := by
    have hh : ContinuousOn (fun x : ℝ =>
        (((Real.sqrt ((x-l)*(u-x))/(2*(Real.pi*(n : ℕ))) : ℝ) : ℂ))*S x) (Icc l u) :=
      (show Continuous (fun x : ℝ =>
        (((Real.sqrt ((x-l)*(u-x))/(2*(Real.pi*(n : ℕ))) : ℝ) : ℂ))) from by fun_prop).continuousOn.mul hS
    exact hh.congr (fun x hx => hv x hx)
  have heq : hillHminusGapBoundaryAction K q l u = (2/(Real.pi : ℂ)) *
      (∫ x in l..u, (((Real.sqrt ((x-l)*(u-x))/(2*(Real.pi*(n : ℕ))) : ℝ) : ℂ))*S x) := by
    unfold hillHminusGapBoundaryAction
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    exact hv x (by simpa only [uIcc_of_le hlu] using hx)
  refine ⟨hi.intervalIntegrable_of_Icc hlu,?_,?_⟩
  · rw [heq]
    simpa only [ofReal_mul,ofReal_natCast] using
      integral_real_gap_sqrt_weight (Real.pi*(n : ℕ)) l u hlu S
  · rw [heq]
    simpa only [ofReal_mul,ofReal_natCast] using
      norm_real_gap_sqrt_weight_error (Real.pi*(n : ℕ)) l u epsilon (by positivity) hlu S hS
        (fun x hx => hnorm (x : ℂ) (hpair.real_gap_mem_ball x hx))

end NLS.KdV
