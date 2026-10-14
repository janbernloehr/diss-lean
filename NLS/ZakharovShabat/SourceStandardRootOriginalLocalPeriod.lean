import NLS.ZakharovShabat.SourceStandardRootLocalEllipses
import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle
import NLS.ComplexAnalysis.PiecewiseContourOuterPeriod
import NLS.ComplexAnalysis.SegmentIsolatingCircles

/-!
# Local standard-root periods on original contours

Shrinking ellipses identify the exact period on every original disk,
including complex open gaps. Cauchy's formula covers collapsed gaps.
Every original piecewise C¹ circuit then contributes its actual winding.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A local standard-root period on an original circuit is its outer circle period times winding. -/
theorem SourceCriticalRootPeriodCircle.standardRoot_local_circuit_eq
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (D.center:ℂ) D.radius))
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m)) :
    Γ.integral (fun z => f z/sourceStandardRoot hp hp1 ψ m z) =
      (∮ z in C((D.center:ℂ),D.radius), f z/sourceStandardRoot hp hp1 ψ m z)*
        Γ.windingIntegral (sourceStandardRootMidpoint hp hp1 ψ m) := by
  obtain ⟨r,s,hr,hrs,hsR,hgap⟩ := exists_nested_radii_of_segment_subset_ball _ _ (D.center:ℂ) D.radius D.gap
  have hquot : AnalyticOnNhd ℂ (fun z => f z/sourceStandardRoot hp hp1 ψ m z)
      (closedBall (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m) := by
    intro z hz
    exact (hf z hz.1).div (sourceStandardRoot_analyticAt hp hp1 ψ m z hz.2)
      (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z hz.2)
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ m
  have hcompact : IsCompact (sourcePeriodicSegment hp hp1 ψ m) := by
    rw [← sourceStandardRoot_gapSegment_eq_periodicSegment]
    exact standardRootGapSegment_compact _ _
  exact Γ.integral_eq_outerCircleIntegral_mul_winding_of_starConvex_cut _ (D.center:ℂ)
    _ r D.radius hr (hrs.trans hsR) _ hcompact.isClosed
    hmid ((convex_segment _ _).starConvex hmid) hgap hquot hΓ

/-- The exact cosine-average formula on an original circle, including complex and collapsed gaps. -/
theorem SourceCriticalRootPeriodCircle.standardRoot_local_circle_period
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (D.center:ℂ) D.radius)) :
    (∮ z in C((D.center:ℂ),D.radius), f z/sourceStandardRoot hp hp1 ψ m z) =
      (-(2*(Real.pi:ℂ))*Complex.I)*(∫ t in (0:ℝ)..1,
        f (sourceStandardRootMidpoint hp hp1 ψ m+
          sourceStandardRootHalfGap hp hp1 ψ m*(Real.cos ((2*Real.pi)*t):ℂ))) := by
  by_cases hg : sourceStandardRootHalfGap hp hp1 ψ m = 0
  · have hτ := D.gap (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m)
    have hc : (∮ z in C((D.center:ℂ),D.radius),
        (z-sourceStandardRootMidpoint hp hp1 ψ m)⁻¹*f z) =
        (2*(Real.pi:ℂ)*Complex.I)*f (sourceStandardRootMidpoint hp hp1 ψ m) := by
      simpa only [smul_eq_mul] using hf.differentiableOn.circleIntegral_sub_inv_smul hτ
    have he : (fun z => f z/sourceStandardRoot hp hp1 ψ m z) =
        (fun z => (-1:ℂ)*((z-sourceStandardRootMidpoint hp hp1 ψ m)⁻¹*f z)) := by
      funext z
      rw [sourceStandardRoot_eq_normalized_halfGap,hg]
      simp only [mul_zero,zero_pow (by decide : (2:ℕ) ≠ 0),normalizedStandardRoot_zeroGap]
      rw [div_eq_mul_inv, ← neg_sub z (sourceStandardRootMidpoint hp hp1 ψ m), inv_neg]
      ring
    rw [he,circleIntegral.integral_const_mul,hc]
    simp only [hg,zero_mul,add_zero,intervalIntegral.integral_const,sub_zero,one_smul]
    ring
  · have hgap : standardRootGapSegment (sourceStandardRootMidpoint hp hp1 ψ m)
        (sourceStandardRootHalfGap hp hp1 ψ m) ⊆ ball (D.center:ℂ) D.radius := by
      rw [sourceStandardRoot_gapSegment_eq_periodicSegment]
      exact D.gap
    obtain ⟨R,hR,hperiod⟩ := exists_standardRootEllipse_local_period
      (sourceStandardRootMidpoint hp hp1 ψ m) (sourceStandardRootHalfGap hp hp1 ψ m) hg
      (ball (D.center:ℂ) D.radius) isOpen_ball hgap f (hf.mono ball_subset_closedBall)
    let r : ℝ := (1+R)/2
    have hr : 1 < r := by dsimp [r]; linarith
    obtain ⟨hin,he⟩ := hperiod r hr (by dsimp [r]; linarith)
    rw [sourceStandardRoot_gapSegment_eq_periodicSegment] at hin
    have he' : (sourceStandardRootEllipseLoop hp hp1 ψ m r (by linarith)).integral
        (fun z => f z/sourceStandardRoot hp hp1 ψ m z) =
        (-(2*(Real.pi:ℂ))*Complex.I)*(∫ t in (0:ℝ)..1,
          f (sourceStandardRootMidpoint hp hp1 ψ m+
            sourceStandardRootHalfGap hp hp1 ψ m*(Real.cos ((2*Real.pi)*t):ℂ))) := by
      simpa only [sourceStandardRootEllipseLoop,sourceStandardRoot_eq_normalized_halfGap] using he
    rw [D.standardRoot_local_circuit_eq f hf (sourceStandardRootEllipseLoop hp hp1 ψ m r (by linarith)) hin,
      sourceStandardRootEllipseLoop_winding hp hp1 ψ m hg r hr,mul_one] at he'
    exact he'

/-- The exact cosine-average formula for arbitrary original circuit winding. -/
theorem SourceCriticalRootPeriodCircle.standardRoot_local_circuit_period
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (D.center:ℂ) D.radius))
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m)) :
    Γ.integral (fun z => f z/sourceStandardRoot hp hp1 ψ m z) =
      ((-(2*(Real.pi:ℂ))*Complex.I)*(∫ t in (0:ℝ)..1,
        f (sourceStandardRootMidpoint hp hp1 ψ m+
          sourceStandardRootHalfGap hp hp1 ψ m*(Real.cos ((2*Real.pi)*t):ℂ))))*
            Γ.windingIntegral (sourceStandardRootMidpoint hp hp1 ψ m) := by
  rw [D.standardRoot_local_circuit_eq f hf Γ hΓ,D.standardRoot_local_circle_period f hf]

end NLS.ZakharovShabat
