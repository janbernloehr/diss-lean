import NLS.KdV.HillOriginalDerivativeBijectivity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Topology.IsLocalHomeomorph

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.KdV

/-- The ACTUAL original map has its ACTUAL invertible strict derivative
at EVERY original mean-zero L2 source. -/
theorem hasStrictFDerivAt_hillOriginalMeanZeroRealSpectralMap
    (q : hillRealMeanZeroSourceSubmodule) :
    HasStrictFDerivAt hillOriginalMeanZeroRealSpectralMap (hillOriginalMeanZeroDerivativeEquiv q).toContinuousLinearMap q :=
  (analyticOnNhd_hillOriginalMeanZeroRealSpectralMap q (mem_univ _)).hasStrictFDerivAt

/-- A local inverse chart for the ACTUAL original map at ANY source,
with its original real Banach norm and literal physical coordinates. -/
def hillOriginalLocalChart (q : hillRealMeanZeroSourceSubmodule) :
    OpenPartialHomeomorph hillRealMeanZeroSourceSubmodule (lp (fun _ : ℕ => ℂ) 2) :=
  (hasStrictFDerivAt_hillOriginalMeanZeroRealSpectralMap q).toOpenPartialHomeomorph
    hillOriginalMeanZeroRealSpectralMap

@[simp] theorem hillOriginalLocalChart_coe (q : hillRealMeanZeroSourceSubmodule) :
    (hillOriginalLocalChart q : hillRealMeanZeroSourceSubmodule → lp (fun _ : ℕ => ℂ) 2) =
      hillOriginalMeanZeroRealSpectralMap := rfl

theorem hillOriginalLocalChart_mem_source (q : hillRealMeanZeroSourceSubmodule) :
    q ∈ (hillOriginalLocalChart q).source :=
  (hasStrictFDerivAt_hillOriginalMeanZeroRealSpectralMap q).mem_toOpenPartialHomeomorph_source

/-- The ACTUAL original mean-zero spectral map is a local homeomorphism
EVERYWHERE; no inverse map is supplied in the hypotheses. -/
theorem isLocalHomeomorph_hillOriginalMeanZeroRealSpectralMap :
    IsLocalHomeomorph hillOriginalMeanZeroRealSpectralMap :=
  fun q => ⟨hillOriginalLocalChart q,hillOriginalLocalChart_mem_source q,rfl⟩

/-- Every actual local inverse is real Banach analytic at its original
spectral base value, including sources with collapsed spectral gaps. -/
theorem analyticAt_hillOriginalLocalInverse (q : hillRealMeanZeroSourceSubmodule) :
    AnalyticAt ℝ (hillOriginalLocalChart q).symm (hillOriginalMeanZeroRealSpectralMap q) := by
  obtain ⟨p,hp⟩ := analyticOnNhd_hillOriginalMeanZeroRealSpectralMap q (mem_univ _)
  let e := hillOriginalMeanZeroDerivativeEquiv q
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℝ hillRealMeanZeroSourceSubmodule
      (lp (fun _ : ℕ => ℂ) 2)).symm e :=
    (continuousMultilinearCurryFin1 ℝ hillRealMeanZeroSourceSubmodule
      (lp (fun _ : ℕ => ℂ) 2)).eq_symm_apply.mpr hp.fderiv_eq.symm
  exact ((hillOriginalLocalChart q).hasFPowerSeriesAt_symm
    (hillOriginalLocalChart_mem_source q) hp hp1).analyticAt

end NLS.KdV
