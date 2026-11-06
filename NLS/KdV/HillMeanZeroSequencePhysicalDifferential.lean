import NLS.KdV.HillOriginalMeanZeroSpectralDerivative
import NLS.KdV.HillOriginalSequencePhysicalDifferential

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The derivative of the ACTUAL original mean-zero map is the restriction
of the original full real derivative, at EVERY source. -/
theorem hillOriginalMeanZeroRealSpectralMap_fderiv_restriction
    (q : hillRealMeanZeroSourceSubmodule) :
    fderiv ℝ hillOriginalMeanZeroRealSpectralMap q =
      (fderiv ℝ hillOriginalRealSpectralMap q.val).comp hillRealMeanZeroSourceSubmodule.subtypeL := by
  let L := hillRealMeanZeroSourceSubmodule.subtypeL
  have hd := ((hasFDerivAt_hillOriginalRealSpectralMap (L q)).comp q L.hasFDerivAt).fderiv
  exact hd

/-- Each ACTUAL original mean-zero coordinate differential at EVERY source
is the physically matched H-minus-one Cartesian derivative, with its fixed
sqrt(2*pi*n) normalization. -/
theorem hillOriginalMeanZeroRealSpectralMap_coordinate_fderiv
    (q : hillRealMeanZeroSourceSubmodule) (k : ℕ) (G : PeriodOneHminusOne → ℂ)
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val.val))
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q.val.val,q.val.property⟩ : RealPeriodOneHillPotential),
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian true ⟨k+1,by omega⟩ p)
    (h : hillRealMeanZeroSourceSubmodule) :
    (fderiv ℝ hillOriginalMeanZeroRealSpectralMap q h) k =
      (Real.sqrt (2*Real.pi*(k+1 : ℕ)) : ℂ)*
        (fderiv ℂ G (hillOriginalHminusSource q.val.val)) (hillOriginalRealHminusInclusion h.val) := by
  have hs := hillOriginalRealSpectralMap_coordinate_fderiv q.val k G hG hGM
  have he := congrArg (fun L : hillRealSourceSubmodule →L[ℝ] ℂ => L h.val) hs
  rw [hillOriginalMeanZeroRealSpectralMap_fderiv_restriction]
  calc
    _ = (lp.evalCLM (𝕜 := ℂ) (fun _ : ℕ => ℂ) 2 k)
        ((fderiv ℝ hillOriginalRealSpectralMap q.val) h.val) := rfl
    _ = _ := by simpa using he

end NLS.KdV
