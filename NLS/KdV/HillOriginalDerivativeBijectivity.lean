import NLS.KdV.HillOriginalDerivativeSurjectivity
import NLS.FunctionalAnalysis.SurjectiveOperatorConnectedFamily

noncomputable section
set_option autoImplicit false
open Set
namespace NLS.KdV

/-- The ACTUAL original spectral derivative is a bounded isomorphism at
EVERY original real mean-zero source, including every collapsed gap.
Surjectivity, norm continuity and zero-source injectivity are all proved. -/
theorem bijective_fderiv_hillOriginalMeanZeroRealSpectralMap
    (q : hillRealMeanZeroSourceSubmodule) :
    Function.Bijective (fderiv ℝ hillOriginalMeanZeroRealSpectralMap q) := by
  have hc : Continuous (fderiv ℝ hillOriginalMeanZeroRealSpectralMap) :=
    analyticOnNhd_hillOriginalMeanZeroRealSpectralMap.fderiv.continuous
  exact NLS.FunctionalAnalysis.bijective_connected_family_of_surjective _ hc
    surjective_fderiv_hillOriginalMeanZeroRealSpectralMap 0
    injective_hillOriginalMeanZeroDerivativeAtZero q

/-- The same ACTUAL original derivative, promoted to a continuous linear
equivalence only after proving its bijectivity at every source. -/
def hillOriginalMeanZeroDerivativeEquiv (q : hillRealMeanZeroSourceSubmodule) :
    hillRealMeanZeroSourceSubmodule ≃L[ℝ] lp (fun _ : ℕ => ℂ) 2 :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ hillOriginalMeanZeroRealSpectralMap q)
    (LinearMap.ker_eq_bot.mpr (bijective_fderiv_hillOriginalMeanZeroRealSpectralMap q).1)
    (LinearMap.range_eq_top.mpr (bijective_fderiv_hillOriginalMeanZeroRealSpectralMap q).2)

@[simp] theorem hillOriginalMeanZeroDerivativeEquiv_apply
    (q h : hillRealMeanZeroSourceSubmodule) :
    hillOriginalMeanZeroDerivativeEquiv q h = fderiv ℝ hillOriginalMeanZeroRealSpectralMap q h := rfl

end NLS.KdV
