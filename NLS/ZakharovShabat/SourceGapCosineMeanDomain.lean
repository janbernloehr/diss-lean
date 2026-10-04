import NLS.ComplexAnalysis.ParametricCosineMeanSegment
import NLS.ZakharovShabat.SourceGapCosineMeanAnalytic

/-! # Cosine means on a common complex source domain

Symmetric endpoint analyticity and regularity along the actual segment
suffice at every complex source. The domain need not shrink separately
for each numerator, moment order, or open/closed gap transition.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A cosine mean is analytic throughout a source domain on which its
actual segment avoids the other gaps and its symmetric coordinates are
analytic. No real-source or nonzero-gap assumption is needed. -/
theorem analyticOnNhd_sourceGapCosineMean_of_segment
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (U : Set (CoeffPair p))
    (g : ℂ × CoeffPair p → ℂ)
    (hD : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 U k))
    (hg : AnalyticOnNhd ℂ g (sourceStandardRootOmittedJointDomain hp hp1 U k))
    (hτ : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ k) U)
    (hγ : AnalyticOnNhd ℂ (fun ψ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2) U)
    (hsegment : ∀ ψ ∈ U, sourcePeriodicSegment hp hp1 ψ k ⊆ sourceStandardRootOmittedDomain hp hp1 ψ k) :
    AnalyticOnNhd ℂ (sourceGapCosineMean hp hp1 k g) U := by
  intro ψ hψ
  have hhalf : AnalyticAt ℂ (fun χ => (sourceStandardRootHalfGap hp hp1 χ k)^2) ψ := by
    have he : (fun χ => (sourceStandardRootHalfGap hp hp1 χ k)^2) =
        fun χ => (canonicalPeriodicGap hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) k)^2/4 := by
      funext χ
      unfold sourceStandardRootHalfGap
      ring
    rw [he]
    exact (hγ ψ hψ).div_const
  apply analyticAt_parametricCosineMean_of_squared_gap_segment g
    (fun χ => sourceStandardRootMidpoint hp hp1 χ k)
    (fun χ => sourceStandardRootHalfGap hp hp1 χ k) _ hD hg ψ (hτ ψ hψ) hhalf
  intro θ _
  refine ⟨hψ,hsegment ψ hψ ?_⟩
  rw [sourcePeriodicSegment_eq_midpoint_segment]
  simpa only [cosineGapPoint,← Complex.ofReal_cos] using
    cosineGapPoint_real_mem_segment (sourceStandardRootMidpoint hp hp1 ψ k)
      (sourceStandardRootHalfGap hp hp1 ψ k) θ

end NLS.ZakharovShabat
