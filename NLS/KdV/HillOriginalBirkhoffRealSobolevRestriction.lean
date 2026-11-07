import NLS.KdV.HillRealSobolevBirkhoffTarget
import NLS.KdV.HillRealWeightedInclusion

noncomputable section
set_option autoImplicit false
namespace NLS.KdV

def hillOriginalBirkhoffRealSobolevRestriction (s : ℝ) (hs : 0 ≤ s)
    (p : RealHillWeightedPotential (SpectralWeight.piSobolev s hs)) (hmean : p.val.val 0 = 0) :
    HillBirkhoffRealSobolevSpace s :=
  hillCorollaryTarget s hs
    (hillOriginalBirkhoffWeightedRestriction (SpectralWeight.corollaryWeight s hs)
      (hillRealWeightedInclusion _ _ (SpectralWeight.corollaryWeight_le s hs) p)
      (by simpa only [hillRealWeightedInclusion_apply] using hmean))

/-- The exact homogeneous restriction retains the raw pairs of the one fixed
global physical map. Neither a new spectral map nor an equivalent norm is used. -/
theorem hillOriginalBirkhoffRealSobolevRestriction_coordinates (s : ℝ) (hs : 0 ≤ s)
    (p : RealHillWeightedPotential (SpectralWeight.piSobolev s hs)) (hmean : p.val.val 0 = 0) (k : ℕ) :
    (hillOriginalBirkhoffRealSobolevRestriction s hs p hmean).val k =
      (hillOriginalBirkhoffMap
        (hillOriginalWeightedMeanZeroSource (SpectralWeight.piSobolev s hs) p hmean)).val k := by
  dsimp only [hillOriginalBirkhoffRealSobolevRestriction]
  rw [hillCorollaryTarget_val]
  change (hillOriginalBirkhoffMap _).val k = _
  rw [hillOriginalWeightedMeanZeroSource_inclusion]

end NLS.KdV
