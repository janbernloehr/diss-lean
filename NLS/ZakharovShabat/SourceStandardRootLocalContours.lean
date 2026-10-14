import NLS.ZakharovShabat.SourceStandardRootOriginalLocalPeriod

/-!
# Admissible contours in arbitrary analytic gap neighborhoods

Noncollapsed gaps use shrinking ellipses; collapsed gaps use small circles.
Both constructions give genuine winding-one contours and the exact source
standard-root period while staying inside the supplied analytic region.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Cauchy's formula for a collapsed source standard root on a local enclosing circle. -/
theorem sourceStandardRoot_collapsed_circle_period (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (hg : sourceStandardRootHalfGap hp hp1 ψ m = 0)
    (f : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c r)
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) :
    (∮ z in C(c,r), f z/sourceStandardRoot hp hp1 ψ m z) =
      (-(2*(Real.pi:ℂ))*Complex.I)*f (sourceStandardRootMidpoint hp hp1 ψ m) := by
  have hc : (∮ z in C(c,r), (z-sourceStandardRootMidpoint hp hp1 ψ m)⁻¹*f z) =
      (2*(Real.pi:ℂ)*Complex.I)*f (sourceStandardRootMidpoint hp hp1 ψ m) := by
    simpa only [smul_eq_mul] using hf.differentiableOn.circleIntegral_sub_inv_smul hmid
  have he : (fun z => f z/sourceStandardRoot hp hp1 ψ m z) =
      (fun z => (-1:ℂ)*((z-sourceStandardRootMidpoint hp hp1 ψ m)⁻¹*f z)) := by
    funext z
    rw [sourceStandardRoot_eq_normalized_halfGap,hg]
    simp only [mul_zero,zero_pow (by decide : (2:ℕ) ≠ 0),normalizedStandardRoot_zeroGap]
    rw [div_eq_mul_inv,← neg_sub z (sourceStandardRootMidpoint hp hp1 ψ m),inv_neg]
    ring
  rw [he,circleIntegral.integral_const_mul,hc]
  ring

/-- Every analytic source-gap neighborhood admits a winding-one contour with the exact local period.
No entire extension or filled original disk is required, and collapse is included. -/
theorem exists_sourceStandardRoot_local_period (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (U : Set ℂ) (hU : IsOpen U)
    (hgap : sourcePeriodicSegment hp hp1 ψ m ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    ∃ Γ : PiecewiseC1Loop, Γ.Inside (U \ sourcePeriodicSegment hp hp1 ψ m) ∧
      Γ.windingIntegral (sourceStandardRootMidpoint hp hp1 ψ m) = 1 ∧
      Γ.integral (fun z => f z/sourceStandardRoot hp hp1 ψ m z) =
        (-(2*(Real.pi:ℂ))*Complex.I)*(∫ t in (0:ℝ)..1,
          f (sourceStandardRootMidpoint hp hp1 ψ m+
            sourceStandardRootHalfGap hp hp1 ψ m*(Real.cos ((2*Real.pi)*t):ℂ))) := by
  by_cases hg : sourceStandardRootHalfGap hp hp1 ψ m = 0
  · let τ := sourceStandardRootMidpoint hp hp1 ψ m
    have hτ : τ ∈ U := hgap (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m)
    obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU τ hτ
    let r : ℝ := ε/2
    have hr : 0 < r := by dsimp [r]; positivity
    have hclosed : closedBall τ r ⊆ U := by
      intro z hz
      apply hεU
      have hd := mem_closedBall.mp hz
      apply mem_ball.mpr
      dsimp [r] at hd
      linarith
    have hsingleton : sourcePeriodicSegment hp hp1 ψ m = {τ} := by
      rw [← sourceStandardRoot_gapSegment_eq_periodicSegment]
      ext z
      constructor
      · rintro ⟨t,ht,he⟩
        simpa only [hg,zero_mul,add_zero,mem_singleton_iff] using he.symm
      · intro hz
        refine ⟨0,by norm_num,?_⟩
        simpa only [hg,zero_mul,add_zero,mem_singleton_iff] using (mem_singleton_iff.mp hz).symm
    refine ⟨PiecewiseC1Loop.circle τ r,?_,PiecewiseC1Loop.windingIntegral_circle τ τ r (by simpa [τ] using hr),?_⟩
    · intro i t
      have hs : (PiecewiseC1Loop.circle τ r).edge i t ∈ sphere τ r :=
        circleMap_mem_sphere τ hr.le ((2*Real.pi)*(t:ℝ))
      refine ⟨hclosed (sphere_subset_closedBall hs),?_⟩
      rw [hsingleton,mem_singleton_iff]
      intro he
      have hd := mem_sphere.mp hs
      rw [he,dist_self] at hd
      linarith
    · rw [PiecewiseC1Loop.integral_circle,sourceStandardRoot_collapsed_circle_period hp hp1 ψ m hg f τ r
        (by simpa [τ] using hr) (hf.mono hclosed)]
      simp only [hg,zero_mul,add_zero,intervalIntegral.integral_const,sub_zero,one_smul]
  · have hgap' : standardRootGapSegment (sourceStandardRootMidpoint hp hp1 ψ m)
        (sourceStandardRootHalfGap hp hp1 ψ m) ⊆ U := by
      rwa [sourceStandardRoot_gapSegment_eq_periodicSegment]
    obtain ⟨R,hR,hperiod⟩ := exists_standardRootEllipse_local_period
      (sourceStandardRootMidpoint hp hp1 ψ m) (sourceStandardRootHalfGap hp hp1 ψ m) hg U hU hgap' f hf
    let r : ℝ := (1+R)/2
    have hr : 1 < r := by dsimp [r]; linarith
    obtain ⟨hin,he⟩ := hperiod r hr (by dsimp [r]; linarith)
    rw [sourceStandardRoot_gapSegment_eq_periodicSegment] at hin
    refine ⟨sourceStandardRootEllipseLoop hp hp1 ψ m r (by linarith),hin,
      sourceStandardRootEllipseLoop_winding hp hp1 ψ m hg r hr,?_⟩
    simpa only [sourceStandardRootEllipseLoop,sourceStandardRoot_eq_normalized_halfGap] using he

end NLS.ZakharovShabat
