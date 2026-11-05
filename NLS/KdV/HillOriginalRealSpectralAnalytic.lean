import NLS.KdV.HillOriginalBaseSpectralSequence
import NLS.KdV.HillRealSourceSubmodule
import NLS.KdV.HillGeneralWeightedCartesianAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- The actual original base Cartesian map on the original real Banach source. -/
def hillOriginalRealSpectralMap (q : hillRealSourceSubmodule) : lp (fun _ : ℕ => ℂ) 2 :=
  hillOriginalBaseSpectralSequence ⟨q.val,q.property⟩

/-- The full original spectral sequence is real Banach analytic at EVERY
original real L2 source. The exact native restriction is used, rather
than a replacement map inferred from norm estimates. -/
theorem analyticOnNhd_hillOriginalRealSpectralMap :
    AnalyticOnNhd ℝ hillOriginalRealSpectralMap univ := by
  intro q _
  let Q : RealPeriodOneHillPotential := ⟨q.val,q.property⟩
  let P := hillOriginalNativeRealSource Q
  obtain ⟨F,hF,hFM⟩ := exists_hillWeightedSpectralSequence_analytic_at_real_source
    (by simp) (by intro k; simp) SpectralWeight.one P
  let L : hillRealSourceSubmodule →L[ℝ] WeightedCoeff SpectralWeight.one.doubleIndex.toWeight 2 :=
    ((hillPeriodOneRestriction SpectralWeight.one).restrictScalars ℝ).comp hillRealSourceSubmodule.subtypeL
  have hA : AnalyticAt ℝ (fun r : hillRealSourceSubmodule => F (L r)) q :=
    (hF.restrictScalars (𝕜 := ℝ)).comp (f := L) (L.analyticAt q)
  have hQ : Continuous (fun r : hillRealSourceSubmodule =>
      hillOriginalNativeRealSource (⟨r.val,r.property⟩ : RealPeriodOneHillPotential)) :=
    L.continuous.subtype_mk _
  exact hA.congr (hQ.continuousAt.tendsto.eventually hFM)

/-- The actual original spectral sequence has a bounded real derivative
at EVERY original real L2 source, including every closed gap. -/
theorem hasFDerivAt_hillOriginalRealSpectralMap (q : hillRealSourceSubmodule) :
    HasFDerivAt hillOriginalRealSpectralMap (fderiv ℝ hillOriginalRealSpectralMap q) q :=
  (analyticOnNhd_hillOriginalRealSpectralMap q (mem_univ _)).differentiableAt.hasFDerivAt

end NLS.KdV
