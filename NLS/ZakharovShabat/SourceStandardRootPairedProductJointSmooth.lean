import NLS.ZakharovShabat.SourceStandardRootPairedJointDomain
import NLS.ComplexAnalysis.LocalAnalyticApproximationOn

/-!
# Joint complex smoothness of the paired standard-root product

On the common open moving-gap complement, analytic finite paired cutoffs
converge uniformly on an actual ball around each point. Banach-space
Schwarz estimates pass this convergence to the full Fréchet derivatives;
iteration makes the infinite product complex smooth there.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On one connected almost-real source domain, the infinite paired
product is jointly complex smooth on the open moving-gap complement,
and the derivatives of its finite cutoffs converge uniformly on a
smaller joint ball around every point. -/
theorem exists_global_source_smooth_pairedJointProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      IsOpen (sourceStandardRootPairedJointDomain hp hp1 W) ∧
      ContDiffOn ℂ ∞ (sourceStandardRootPairedJointProduct hp hp1)
        (sourceStandardRootPairedJointDomain hp hp1 W) ∧
      ∀ t ∈ sourceStandardRootPairedJointDomain hp hp1 W,
        ∃ r : ℝ, 0 < r ∧
          Metric.ball t r ⊆ sourceStandardRootPairedJointDomain hp hp1 W ∧
          TendstoUniformlyOn
            (fun N => fderiv ℂ (sourceStandardRootPairedJointPartialProduct hp hp1 N))
            (fderiv ℂ (sourceStandardRootPairedJointProduct hp hp1))
            atTop (Metric.ball t r) := by
  obtain ⟨W, hWopen, hWconnected, hreal, hDopen, hfinite, _⟩ :=
    exists_global_source_open_locallyUniform_pairedJointProduct hp hp1
  have happrox : NLS.ComplexAnalysis.HasLocalUniformAnalyticApproximationOn
      (sourceStandardRootPairedJointPartialProduct hp hp1)
      (sourceStandardRootPairedJointProduct hp hp1)
      (sourceStandardRootPairedJointDomain hp hp1 W) :=
    NLS.ComplexAnalysis.HasLocalUniformAnalyticApproximationOn.of_open_local_uniform
      hDopen hfinite (fun t ht =>
        exists_local_uniform_sourceStandardRootPairedProduct hp hp1 t.2 t.1
          (fun N => (hfinite N t ht).continuousAt))
  exact ⟨W, hWopen, hWconnected, hreal, hDopen,
    happrox.contDiffOn, fun t ht => happrox.uniform_fderiv t ht⟩

end NLS.ZakharovShabat
