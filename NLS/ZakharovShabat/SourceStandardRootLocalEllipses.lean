import NLS.ZakharovShabat.SourceStandardRootLocalEllipseEstimates
import NLS.ZakharovShabat.SourceStandardRootPiecewiseContour
import NLS.ZakharovShabat.SourceStandardRootGapSideEndpoint

/-!
# Local ellipse contours for the actual source standard roots

Every noncollapsed source gap has winding-one ellipse contours in any
prescribed analytic neighborhood. The maximum and mean-value statements
use the actual root and actual source gap, for arbitrary complex sources.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceStandardRoot_eq_normalized_halfGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (z : ℂ) :
    sourceStandardRoot hp hp1 ψ m z = normalizedStandardRoot
      (sourceStandardRootMidpoint hp hp1 ψ m) ((2*sourceStandardRootHalfGap hp hp1 ψ m)^2) z := by
  unfold sourceStandardRoot
  congr 1
  dsimp [sourceStandardRootHalfGap]
  ring

/-- A positive ellipse around the selected actual source gap. -/
def sourceStandardRootEllipseLoop (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (r : ℝ) (hr : 0 < r) : PiecewiseC1Loop :=
  standardRootEllipseLoop (sourceStandardRootMidpoint hp hp1 ψ m)
    (sourceStandardRootHalfGap hp hp1 ψ m) r hr

/-- The source ellipse avoids the selected gap for every radius greater than one. -/
theorem sourceStandardRootEllipseLoop_avoids (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (hg : sourceStandardRootHalfGap hp hp1 ψ m ≠ 0)
    (r : ℝ) (hr : 1 < r) :
    (sourceStandardRootEllipseLoop hp hp1 ψ m r (by linarith)).Inside
      (sourcePeriodicSegment hp hp1 ψ m)ᶜ := by
  apply standardRootEllipseLoop_inside
  intro t ht
  rw [← sourceStandardRoot_gapSegment_eq_periodicSegment]
  exact standardRootEllipseMap_not_mem_gap _ _ r t hg hr

/-- The ellipse has winding one around the actual midpoint. -/
theorem sourceStandardRootEllipseLoop_winding (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (hg : sourceStandardRootHalfGap hp hp1 ψ m ≠ 0)
    (r : ℝ) (hr : 1 < r) :
    (sourceStandardRootEllipseLoop hp hp1 ψ m r (by linarith)).windingIntegral
      (sourceStandardRootMidpoint hp hp1 ψ m) = 1 := by
  let Γ := sourceStandardRootEllipseLoop hp hp1 ψ m r (by linarith)
  have hv : Γ.integral (fun z => (sourceStandardRoot hp hp1 ψ m z)⁻¹) =
      -(2*(Real.pi:ℂ))*Complex.I := by
    simpa [Γ,sourceStandardRootEllipseLoop,sourceStandardRoot_eq_normalized_halfGap,
      intervalIntegral.integral_const] using
      standardRootEllipseLoop_weighted_integral
        (sourceStandardRootMidpoint hp hp1 ψ m) (sourceStandardRootHalfGap hp hp1 ψ m)
        r hr hg (fun _ => 1)
  have hn : Γ.normalizedIntegral (fun z => (sourceStandardRoot hp hp1 ψ m z)⁻¹) = -1 := by
    rw [PiecewiseC1Loop.normalizedIntegral,hv]
    field_simp
  have h := normalized_sourceStandardRoot_inv_piecewiseIntegral_eq_neg_winding hp hp1 ψ m Γ
    (sourceStandardRootEllipseLoop_avoids hp hp1 ψ m hg r hr)
  rw [hn] at h
  exact neg_injective h.symm

/-- Lemma 12.3 on a family of actual winding-one ellipses in an arbitrary analytic neighborhood. -/
theorem exists_sourceStandardRoot_local_ellipse_estimates (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (hg : sourceStandardRootHalfGap hp hp1 ψ m ≠ 0)
    (U : Set ℂ) (hU : IsOpen U) (hgap : sourcePeriodicSegment hp hp1 ψ m ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    ∃ R : ℝ, 1 < R ∧ ∃ z ∈ sourcePeriodicSegment hp hp1 ψ m,
      IsMaxOn (fun w => ‖f w‖) (sourcePeriodicSegment hp hp1 ψ m) z ∧
      ∀ r : ℝ, ∀ hr : 1 < r, r ≤ R →
        (sourceStandardRootEllipseLoop hp hp1 ψ m r (by linarith)).Inside
          (U \ sourcePeriodicSegment hp hp1 ψ m) ∧
        (sourceStandardRootEllipseLoop hp hp1 ψ m r (by linarith)).windingIntegral
          (sourceStandardRootMidpoint hp hp1 ψ m) = 1 ∧
        ‖(2*(Real.pi:ℂ))⁻¹*(sourceStandardRootEllipseLoop hp hp1 ψ m r (by linarith)).integral
          (fun w => f w/sourceStandardRoot hp hp1 ψ m w)‖ ≤ ‖f z‖ ∧
        ((∀ w ∈ sourcePeriodicSegment hp hp1 ψ m, (f w).im = 0) →
          ∃ μ ∈ sourcePeriodicSegment hp hp1 ψ m,
            (sourceStandardRootEllipseLoop hp hp1 ψ m r (by linarith)).normalizedIntegral
              (fun w => f w/sourceStandardRoot hp hp1 ψ m w) = -f μ) := by
  have hgap' : standardRootGapSegment (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m) ⊆ U := by
    rwa [sourceStandardRoot_gapSegment_eq_periodicSegment]
  obtain ⟨R,hR,z,hz,hmax,hest⟩ := exists_standardRootEllipse_local_estimates
    (sourceStandardRootMidpoint hp hp1 ψ m) (sourceStandardRootHalfGap hp hp1 ψ m) hg U hU hgap' f hf
  rw [sourceStandardRoot_gapSegment_eq_periodicSegment] at hz hmax hest
  refine ⟨R,hR,z,hz,hmax,fun r hr hrR => ?_⟩
  obtain ⟨hin,hbound,hmean⟩ := hest r hr hrR
  refine ⟨hin,sourceStandardRootEllipseLoop_winding hp hp1 ψ m hg r hr,?_,?_⟩
  · simpa only [sourceStandardRootEllipseLoop,sourceStandardRoot_eq_normalized_halfGap] using hbound
  · simpa only [sourceStandardRootEllipseLoop,sourceStandardRoot_eq_normalized_halfGap] using hmean

end NLS.ZakharovShabat
