import NLS.KdV.HillHminusOneActionChart
import NLS.KdV.HillHminusOneBoundaryAction

/-! # Real boundary action formulas from an actual valid chart

Pointwise strict near-one normalization suffices. No uniform norm bound
on the entire open spectral disc, extra joint chart, or noncollapsed-gap
hypothesis is needed for the real principal root and its exact gap area.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillHminusActionChartValid.real_gap_factorization
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (l u : ℝ)
    (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ)) (E : ℝ) (hE : E ∈ Icc l u) :
    K ((E : ℂ),q) = -((E : ℂ)-l)*((E : ℂ)-u)*
      hillHminusJointNormalizedGapRoot n r K ((E : ℂ),q)^2/(4*((Real.pi*(n : ℕ) : ℝ) : ℂ)^2) := by
  have hf := h.2.2.2.2.1 (E : ℂ) (hpair.real_gap_mem_ball E hE)
  rw [hpair.gapPolynomial_eq h.1] at hf
  simpa only [ofReal_mul,ofReal_natCast,neg_mul] using hf

theorem HillHminusActionChartValid.real_gap_sqrt_value
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (l u : ℝ)
    (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ)) (E : ℝ) (hE : E ∈ Icc l u) :
    Complex.sqrt (K ((E : ℂ),q)) =
      ((Real.sqrt ((E-l)*(u-E))/(2*(Real.pi*(n : ℕ))) : ℝ) : ℂ)*
        hillHminusJointNormalizedGapRoot n r K ((E : ℂ),q) := by
  exact principalSqrt_real_gap_factor (Real.pi*(n : ℕ)) l u E (by positivity) hE _ _
    (h.2.2.2.2.2.1 (E : ℂ) (hpair.real_gap_mem_ball E hE))
    (h.real_gap_factorization l u hpair E hE)

theorem HillHminusActionChartValid.real_gap_sqrt_continuousOn
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (l u : ℝ)
    (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ)) :
    ContinuousOn (fun E : ℝ => Complex.sqrt (K ((E : ℂ),q))) (Icc l u) := by
  intro E hE
  have hs := continuousAt_principalSqrt_real_gap_factor (Real.pi*(n : ℕ)) l u E
    (by positivity) hE _ _ (h.2.2.2.2.2.1 (E : ℂ) (hpair.real_gap_mem_ball E hE))
    (h.real_gap_factorization l u hpair E hE)
  have hK : ContinuousAt (fun E : ℝ => K ((E : ℂ),q)) E :=
    (h.2.1 (E : ℂ) (hpair.real_gap_mem_ball E hE)).continuousAt.comp
      (f := fun E : ℝ => (E : ℂ)) continuous_ofReal.continuousAt
  exact (hs.comp (f := fun E : ℝ => K ((E : ℂ),q)) hK).continuousWithinAt

theorem HillHminusActionChartValid.boundary_action_eq_ratio
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (l u : ℝ) (hlu : l ≤ u)
    (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ)) :
    hillHminusGapBoundaryAction K q l u =
      (((u-l : ℝ) : ℂ)^2/(8*((Real.pi : ℂ)*(n : ℕ))))*hillHminusNormalizedActionRatio n r K q := by
  have heq : hillHminusGapBoundaryAction K q l u = (2/(Real.pi : ℂ))*
      (∫ E in l..u, ((Real.sqrt ((E-l)*(u-E))/(2*(Real.pi*(n : ℕ))) : ℝ) : ℂ)*
        hillHminusJointNormalizedGapRoot n r K ((E : ℂ),q)) := by
    unfold hillHminusGapBoundaryAction
    congr 1
    apply intervalIntegral.integral_congr
    intro E hE
    exact h.real_gap_sqrt_value l u hpair E (by simpa only [uIcc_of_le hlu] using hE)
  rw [heq,hillHminusNormalizedActionRatio_eq_mean n r h.1 K q (l : ℂ) (u : ℂ) hpair]
  have hm : (fun a : ℝ => hillHminusJointNormalizedGapRoot n r K
      ((((l+u)/2+(u-l)/2*a : ℝ) : ℂ),q)) =
      (fun a : ℝ => hillHminusJointNormalizedGapRoot n r K
        (((l : ℂ)+(u : ℂ))/2+((u : ℂ)-(l : ℂ))/2*(a : ℂ),q)) := by
    funext a
    congr 2
    push_cast
    rfl
  have hi := integral_real_gap_sqrt_weight (Real.pi*(n : ℕ)) l u hlu
    (fun E => hillHminusJointNormalizedGapRoot n r K ((E : ℂ),q))
  rw [hm] at hi
  simpa only [ofReal_mul,ofReal_natCast] using hi

end NLS.KdV
