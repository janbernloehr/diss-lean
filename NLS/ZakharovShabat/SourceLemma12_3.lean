import NLS.ZakharovShabat.SourceStandardRootLocalContours

/-!
# Lemma 12.3 with explicit contour admissibility

Both estimates hold on original circuits when the numerator is analytic
near the filled original disk. Every arbitrary analytic gap neighborhood
also admits a winding-one contour with both estimates. These statements
exclude the interior-pole counterexample recorded in SOURCE_ERRATA.md.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The attained maximum bound and real mean-value conclusion of Lemma 12.3. -/
def SourceLemma12_3Estimates (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (f : ℂ → ℂ) (Γ : PiecewiseC1Loop) : Prop :=
  ∃ z ∈ sourcePeriodicSegment hp hp1 ψ m,
    IsMaxOn (fun w => ‖f w‖) (sourcePeriodicSegment hp hp1 ψ m) z ∧
    ‖(2*(Real.pi:ℂ))⁻¹*Γ.integral (fun w => f w/sourceStandardRoot hp hp1 ψ m w)‖ ≤ ‖f z‖ ∧
    ((∀ w ∈ sourcePeriodicSegment hp hp1 ψ m, (f w).im = 0) →
      ∃ μ ∈ sourcePeriodicSegment hp hp1 ψ m,
        Γ.normalizedIntegral (fun w => f w/sourceStandardRoot hp hp1 ψ m w) = -f μ)

/-- The exact source period implies both estimates, with only continuity and gap reality. -/
theorem sourceLemma12_3_of_period (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (f : ℂ → ℂ) (hf : ContinuousOn f (sourcePeriodicSegment hp hp1 ψ m)) (Γ : PiecewiseC1Loop)
    (hJ : Γ.integral (fun z => f z/sourceStandardRoot hp hp1 ψ m z) =
      (-(2*(Real.pi:ℂ))*Complex.I)*(∫ t in (0:ℝ)..1,
        f (sourceStandardRootMidpoint hp hp1 ψ m+
          sourceStandardRootHalfGap hp hp1 ψ m*(Real.cos ((2*Real.pi)*t):ℂ)))) :
    SourceLemma12_3Estimates hp hp1 ψ m f Γ := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let δ := sourceStandardRootHalfGap hp hp1 ψ m
  have hfc : ContinuousOn f (standardRootGapSegment τ δ) := by
    rwa [sourceStandardRoot_gapSegment_eq_periodicSegment]
  have hne : (standardRootGapSegment τ δ).Nonempty := ⟨τ,⟨0,by norm_num,by simp⟩⟩
  obtain ⟨z,hz,hmax⟩ := (standardRootGapSegment_compact τ δ).exists_isMaxOn hne hfc.norm
  unfold SourceLemma12_3Estimates
  simp only [← sourceStandardRoot_gapSegment_eq_periodicSegment]
  refine ⟨z,hz,hmax,norm_standardRoot_gap_period_le τ δ f _ _ hmax hJ,?_⟩
  intro hreal
  exact standardRoot_gap_period_real_mean_value τ δ f _ hfc hreal hJ

/-- Lemma 12.3 on every original enclosing circle, including all complex collapsed gaps. -/
theorem SourceCriticalRootPeriodCircle.lemma12_3_circle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (D.center:ℂ) D.radius)) :
    SourceLemma12_3Estimates hp hp1 ψ m f (PiecewiseC1Loop.circle (D.center:ℂ) D.radius) := by
  apply sourceLemma12_3_of_period hp hp1 ψ m f
    (hf.continuousOn.mono (D.gap.trans ball_subset_closedBall))
  rw [PiecewiseC1Loop.integral_circle]
  exact D.standardRoot_local_circle_period f hf

/-- Lemma 12.3 on every original winding-one piecewise C¹ circuit. -/
theorem SourceCriticalRootPeriodCircle.lemma12_3_circuit
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (D.center:ℂ) D.radius))
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m))
    (hw : Γ.windingIntegral (sourceStandardRootMidpoint hp hp1 ψ m) = 1) :
    SourceLemma12_3Estimates hp hp1 ψ m f Γ := by
  apply sourceLemma12_3_of_period hp hp1 ψ m f
    (hf.continuousOn.mono (D.gap.trans ball_subset_closedBall))
  rw [D.standardRoot_local_circuit_period f hf Γ hΓ,hw,mul_one]

/-- Every arbitrary analytic gap neighborhood admits an admissible contour satisfying Lemma 12.3. -/
theorem sourceLemma12_3_local (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (U : Set ℂ) (hU : IsOpen U) (hgap : sourcePeriodicSegment hp hp1 ψ m ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    ∃ Γ : PiecewiseC1Loop, Γ.Inside (U \ sourcePeriodicSegment hp hp1 ψ m) ∧
      Γ.windingIntegral (sourceStandardRootMidpoint hp hp1 ψ m) = 1 ∧
      SourceLemma12_3Estimates hp hp1 ψ m f Γ := by
  obtain ⟨Γ,hin,hw,hJ⟩ := exists_sourceStandardRoot_local_period hp hp1 ψ m U hU hgap f hf
  exact ⟨Γ,hin,hw,sourceLemma12_3_of_period hp hp1 ψ m f (hf.continuousOn.mono hgap) Γ hJ⟩

end NLS.ZakharovShabat
