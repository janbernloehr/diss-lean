import NLS.ComplexAnalysis.EndpointPrimitivePeriod
import NLS.ComplexAnalysis.PiecewiseOpenDiscPeriod

/-! # Exact endpoint-root primitive periods for arbitrary circuit winding

Complex endpoints and collapsed gaps are included. Holomorphy is needed
only on the original open disc; no boundary extension or contour shape
is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory NLS.ZakharovShabat
namespace NLS.ComplexAnalysis

theorem endpointPrimitive_circuit_period
    (c t d b : ℂ) (R : ℝ) (hgap : standardRootGapSegment t d ⊆ ball b R)
    (S : ℂ → ℂ) (hS : AnalyticOnNhd ℂ S (ball b R))
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (ball b R \ standardRootGapSegment t d)) :
    Γ.integral (fun z => I/(2*c)*normalizedStandardRoot t ((2*d)^2) z*S z) =
      (-(d^2)/c*(∫ θ in (0 : ℝ)..Real.pi,
        (Real.sin θ : ℂ)^2*S (t+d*(Real.cos θ : ℂ))))*Γ.windingIntegral t := by
  by_cases hd : d = 0
  · subst d
    have he : (fun z => I/(2*c)*normalizedStandardRoot t ((2*(0 : ℂ))^2) z*S z) =
        (fun z => I/(2*c)*(t-z)*S z) := by funext z; simp
    have hF : AnalyticOnNhd ℂ (fun z => I/(2*c)*(t-z)*S z) (ball b R) :=
      (analyticOnNhd_const.mul (analyticOnNhd_const.sub analyticOnNhd_id)).mul hS
    rw [he,Γ.integral_eq_zero_of_convex _ _ isOpen_ball (convex_ball _ _) hF.differentiableOn
      (fun i a => (hΓ i a).1)]
    simp
  · obtain ⟨A,hA,hperiod⟩ := exists_endpointPrimitive_ellipse_period c t d hd
      (ball b R) isOpen_ball hgap S hS
    obtain ⟨hin,hw,he⟩ := hperiod ((1+A)/2) (by linarith) (by linarith)
    let Γ₀ := standardRootEllipseLoop t d ((1+A)/2) (by linarith)
    have hroot : AnalyticOnNhd ℂ (normalizedStandardRoot t ((2*d)^2))
        (ball b R \ standardRootGapSegment t d) := by
      intro z hz
      have hm : ((t-d)+(t+d))/2 = t := by ring
      have hh : ((t+d)-(t-d))^2 = (2*d)^2 := by ring
      simpa only [hm,hh] using analyticOnNhd_standardRoot_off_segment (t-d) (t+d) z
        (by
          change z ∉ segment ℝ (t-d) (t+d)
          rw [← standardRootGapSegment_eq_segment]
          exact hz.2)
    have hF : AnalyticOnNhd ℂ (fun z => I/(2*c)*normalizedStandardRoot t ((2*d)^2) z*S z)
        (ball b R \ standardRootGapSegment t d) :=
      (analyticOnNhd_const.mul hroot).mul (hS.mono (fun _ hz => hz.1))
    have ht : t ∈ standardRootGapSegment t d := ⟨0,by constructor <;> norm_num,by simp⟩
    have hstar : StarConvex ℝ t (standardRootGapSegment t d) := by
      rw [standardRootGapSegment_eq_segment] at ht ⊢
      exact (convex_segment _ _).starConvex ht
    rw [Γ.integral_eq_reference_mul_winding_of_open_disc_cut Γ₀ _ b t R _
      (standardRootGapSegment_compact t d).isClosed ht hstar hgap hF hΓ hin hw,he]

/-- An actual positively oriented circle encloses any complex endpoint segment
inside an open disc, including a collapsed segment. -/
theorem exists_endpointGap_winding_one_contour
    (t d b : ℂ) (R : ℝ) (hgap : standardRootGapSegment t d ⊆ ball b R) :
    ∃ Γ : PiecewiseC1Loop, Γ.Inside (ball b R \ standardRootGapSegment t d) ∧
      Γ.windingIntegral t = 1 := by
  have ht : t ∈ standardRootGapSegment t d := ⟨0,by constructor <;> norm_num,by simp⟩
  have hR : 0 < R := dist_nonneg.trans_lt (mem_ball.mp (hgap ht))
  obtain ⟨s,hs,hKs⟩ := exists_pos_lt_subset_ball hR (standardRootGapSegment_compact t d).isClosed hgap
  let Γ := PiecewiseC1Loop.circle b s
  refine ⟨Γ,?_,PiecewiseC1Loop.windingIntegral_circle b t s (hKs ht)⟩
  intro i a
  have hp : Γ.edge i a ∈ sphere b s := circleMap_mem_sphere b hs.1.le ((2*Real.pi)*(a : ℝ))
  refine ⟨closedBall_subset_ball hs.2 (sphere_subset_closedBall hp),?_⟩
  intro hz
  exact (mem_ball.mp (hKs hz)).ne (mem_sphere.mp hp)

end NLS.ComplexAnalysis
