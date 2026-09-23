import NLS.ZakharovShabat.SourceStandardRootPairedProductJointSmooth
import NLS.ComplexAnalysis.BanachSmoothAnalyticOn

/-!
# Joint analyticity of the paired standard-root product

The locally uniform analytic cutoffs give complex smoothness on the open
moving-gap complement. Local Banach-space Taylor expansion then yields
joint analyticity of the actual infinite product.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On one connected almost-real source domain, the infinite paired product
is jointly analytic on the open moving-gap complement. Its first cutoff
derivatives also converge uniformly on a smaller ball around each point. -/
theorem exists_global_source_analytic_pairedJointProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      IsOpen (sourceStandardRootPairedJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourceStandardRootPairedJointProduct hp hp1)
        (sourceStandardRootPairedJointDomain hp hp1 W) ∧
      ∀ t ∈ sourceStandardRootPairedJointDomain hp hp1 W,
        ∃ r : ℝ, 0 < r ∧
          Metric.ball t r ⊆ sourceStandardRootPairedJointDomain hp hp1 W ∧
          TendstoUniformlyOn
            (fun N => fderiv ℂ (sourceStandardRootPairedJointPartialProduct hp hp1 N))
            (fderiv ℂ (sourceStandardRootPairedJointProduct hp hp1))
            atTop (Metric.ball t r) := by
  obtain ⟨W, hWopen, hWconnected, hreal, hDopen, hsmooth, hderiv⟩ :=
    exists_global_source_smooth_pairedJointProduct hp hp1
  exact ⟨W, hWopen, hWconnected, hreal, hDopen,
    NLS.ComplexAnalysis.analyticOnNhd_of_complexSmoothOn _ hDopen hsmooth,
    hderiv⟩

end NLS.ZakharovShabat
