import NLS.KdV.HillOriginalFourierSurjectivity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Analytic.Inverse

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- Strict differentiability with the actual, now proved invertible,
original Fourier derivative. -/
theorem hasStrictFDerivAt_hillOriginalMeanZeroRealSpectralMap_zero :
    HasStrictFDerivAt hillOriginalMeanZeroRealSpectralMap
      (hillOriginalMeanZeroDerivativeAtZeroEquiv h0q h0r).toContinuousLinearEquiv.toContinuousLinearMap 0 := by
  have h := (analyticOnNhd_hillOriginalMeanZeroRealSpectralMap 0 (mem_univ _)).hasStrictFDerivAt
  exact h

include h0q h0r in
/-- An actual local inverse chart for the ORIGINAL physical spectral map
at the free source, obtained only after proving the Fourier derivative onto. -/
def hillOriginalFreeLocalChart :
    OpenPartialHomeomorph hillRealMeanZeroSourceSubmodule (lp (fun _ : ℕ => ℂ) 2) :=
  (hasStrictFDerivAt_hillOriginalMeanZeroRealSpectralMap_zero h0q h0r).toOpenPartialHomeomorph
    hillOriginalMeanZeroRealSpectralMap

include h0q h0r in
theorem hillOriginalFreeLocalChart_coe :
    (hillOriginalFreeLocalChart h0q h0r : hillRealMeanZeroSourceSubmodule → lp (fun _ : ℕ => ℂ) 2) =
      hillOriginalMeanZeroRealSpectralMap := rfl

include h0q h0r in
theorem hillOriginalFreeLocalChart_zero_mem_source :
    (0 : hillRealMeanZeroSourceSubmodule) ∈ (hillOriginalFreeLocalChart h0q h0r).source :=
  (hasStrictFDerivAt_hillOriginalMeanZeroRealSpectralMap_zero h0q h0r).mem_toOpenPartialHomeomorph_source

include h0q h0r in
/-- The inverse is a genuine two-sided local inverse of the fixed original
spectral map on open neighborhoods of zero in its original Banach spaces. -/
theorem hillOriginalFreeLocalInverse_two_sided :
    (∀ᶠ q in 𝓝 (0 : hillRealMeanZeroSourceSubmodule),
      (hillOriginalFreeLocalChart h0q h0r).symm (hillOriginalMeanZeroRealSpectralMap q) = q) ∧
    (∀ᶠ z in 𝓝 (0 : lp (fun _ : ℕ => ℂ) 2),
      hillOriginalMeanZeroRealSpectralMap ((hillOriginalFreeLocalChart h0q h0r).symm z) = z) := by
  constructor
  · exact (hasStrictFDerivAt_hillOriginalMeanZeroRealSpectralMap_zero h0q h0r).eventually_left_inverse
  · have hh : ∀ᶠ z in 𝓝 (hillOriginalMeanZeroRealSpectralMap 0),
        hillOriginalMeanZeroRealSpectralMap ((hillOriginalFreeLocalChart h0q h0r).symm z) = z :=
      (hasStrictFDerivAt_hillOriginalMeanZeroRealSpectralMap_zero h0q h0r).eventually_right_inverse
    simpa only [hillOriginalMeanZeroRealSpectralMap_zero] using hh

include h0q h0r in
/-- The inverse germ of the fixed ORIGINAL physical map is real Banach
analytic at zero, with no replacement of the map or its Banach norms. -/
theorem analyticAt_hillOriginalFreeLocalInverse :
    AnalyticAt ℝ (hillOriginalFreeLocalChart h0q h0r).symm
      (0 : lp (fun _ : ℕ => ℂ) 2) := by
  obtain ⟨p,hp⟩ := analyticOnNhd_hillOriginalMeanZeroRealSpectralMap 0 (mem_univ _)
  let e := (hillOriginalMeanZeroDerivativeAtZeroEquiv h0q h0r).toContinuousLinearEquiv
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℝ hillRealMeanZeroSourceSubmodule
      (lp (fun _ : ℕ => ℂ) 2)).symm e := by
    exact (continuousMultilinearCurryFin1 ℝ hillRealMeanZeroSourceSubmodule
      (lp (fun _ : ℕ => ℂ) 2)).eq_symm_apply.mpr hp.fderiv_eq.symm

  have hi := (hillOriginalFreeLocalChart h0q h0r).hasFPowerSeriesAt_symm
    (hillOriginalFreeLocalChart_zero_mem_source h0q h0r) hp hp1
  simpa only [hillOriginalFreeLocalChart_coe,hillOriginalMeanZeroRealSpectralMap_zero] using hi.analyticAt

end NLS.KdV
