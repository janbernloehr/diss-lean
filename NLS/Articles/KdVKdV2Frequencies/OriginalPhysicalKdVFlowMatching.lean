import NLS.Articles.KdVKdV2Frequencies.PhysicalKdVFrequencyBridge
import NLS.Articles.KdVKdV2Frequencies.OriginalKdVBirkhoffFlow

/-! The retained original-norm Birkhoff evolution is EXACTLY the same
physical KdV phase evolution whose strong PDE equation and universal
classical-approximation uniqueness are proved independently. -/
noncomputable section
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open GlobalRoughAbelianForwardData

theorem original_source_normalization_native
    (s : ℝ) (hs : -1/2≤s)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    fourierLebesgueSourceNormalization s hs 2 (by simp) (by norm_num) q=
      physicalRealSobolevInclusion (by linarith : (-1:ℝ)≤s)
        ((physicalRealMeanZeroWeightedIsometry (Weight.sobolev s) (Weight.sobolev_neg s)).symm q) := by
  apply Subtype.ext
  change WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))
      (fourierLebesgueSourceInclusion s hs 2 (by simp) (by norm_num) q.val)=
    WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1:ℝ)≤s)
      (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev s) q.val)
  rw [WeightedCoeff.meanZeroSobolevInclusion_projection]
  congr 1
  apply Subtype.ext
  funext j
  simp only [fourierLebesgueSourceInclusion_apply,WeightedCoeff.sobolevInclusion_apply]

theorem original_flow_source_normalization
    (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1/2≤s)
    (G : ℕ+ → Coeff 1 → ℂ) (time : ℝ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    fourierLebesgueSourceNormalization s hs 2 (by simp) (by norm_num)
      (originalKdVBirkhoffFlow D s (by linarith) G time q)=
        nativeKdVSourceFlow D 0 (by norm_num) G time
          (fourierLebesgueSourceNormalization s hs 2 (by simp) (by norm_num) q) := by
  rw [original_source_normalization_native,original_source_normalization_native]
  let e := physicalRealMeanZeroWeightedIsometry (Weight.sobolev s) (Weight.sobolev_neg s)
  change physicalRealSobolevInclusion (by linarith : (-1:ℝ)≤s)
      (e.symm (e (nativeKdVSourceFlow D (s+1) (by linarith) G time (e.symm q))))=_
  rw [e.symm_apply_apply]
  have h := nativeKdVSourceFlow_weak D (s+1) (by linarith) G time (e.symm q)
  simpa only [show s+1-1=s by ring] using h

theorem original_flow_eq_physical_evolution
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (G : ℕ+ → Coeff 1 → ℂ)
    (hB : ∀ n a,B.frequency n a=G n (baseActionNormalization a)+(2*(n:ℂ)*Real.pi)^3)
    (s : ℝ) (hs : -1/2≤s) (time : ℝ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    originalKdVBirkhoffFlow D s (by linarith) G time q=
      D.fourierLebesguePhaseEvolution B s hs 2 (by simp) (by norm_num) time q := by
  apply fourierLebesgueSourceNormalization_injective s hs 2 (by simp) (by norm_num)
  have h := D.fourierLebesguePhaseEvolution_weak_commuting B s hs 2 (by simp) (by norm_num) time q
  exact (original_flow_source_normalization D s hs G time q).trans
    ((native_zero_source_flow_matches_physical D B G hB time _).trans h.symm)

end NLS.Articles.KdVKdV2Frequencies
