import NLS.ZakharovShabat.SourcePsiPiecewiseContour

/-! The actual original circle/winding formula holds for ANY entire
numerator, so comparison contours need not be images of circles. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceCriticalRootPeriodCircle.cutDisk_subset_rootDomain
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  intro z hz k
  by_cases hk : k = m
  · subst k
    exact hz.2
  · exact D.closedBall_subset_omittedDomain (ball_subset_closedBall hz.1) k hk

theorem SourceCriticalRootPeriodCircle.entireNumerator_loop_integral
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F univ) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m)) :
    Γ.integral (fun z => F z/sourceCanonicalRoot hp hp1 ψ z) =
      (∮ z in C((D.center:ℂ),D.radius), F z/sourceCanonicalRoot hp hp1 ψ z)*
        Γ.windingIntegral (sourceStandardRootMidpoint hp hp1 ψ m) := by
  obtain ⟨r,s,hr,hrs,hsR,hgap⟩ := exists_nested_radii_of_segment_subset_ball _ _ (D.center:ℂ) D.radius D.gap
  have hf : AnalyticOnNhd ℂ (fun z => F z/sourceCanonicalRoot hp hp1 ψ z)
      (closedBall (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m) := by
    intro z hz
    have hroot : z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
      intro k
      by_cases hk : k = m
      · subst k
        exact hz.2
      · exact D.closedBall_subset_omittedDomain hz.1 k hk
    exact (hF z (mem_univ _)).div (sourceCanonicalRoot_analyticOnNhd hp hp1 ψ z hroot)
      (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z hroot)
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ m
  exact Γ.integral_eq_outerCircleIntegral_mul_winding_of_starConvex_cut _ (D.center:ℂ)
    _ r D.radius hr (hrs.trans hsR) _ (isCompact_sourcePeriodicSegment hp hp1 ψ m).isClosed
    hmid ((convex_segment _ _).starConvex hmid) hgap hf hΓ

end NLS.ZakharovShabat
