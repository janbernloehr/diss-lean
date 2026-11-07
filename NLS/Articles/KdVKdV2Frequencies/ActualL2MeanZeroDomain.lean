import NLS.Articles.KdVKdV2Frequencies.ActualL2FourierLinearization
import NLS.Articles.KdVKdV2Frequencies.OriginalComplexMeanZeroBirkhoffMap
import NLS.ComplexAnalysis.RestrictAnalyticRealNeighborhood

/-! The literal original mean-zero L2 inclusion lies in the SAME true
complex Birkhoff domain at EVERY real source. -/
noncomputable section
open Set NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem originalL2MeanZeroSource_eq_intrinsic
    (q : complexMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    originalL2MeanZeroSource q=(complexMeanZeroSobolevInclusion (by norm_num : (-1:ℝ)≤0) q).val := by
  apply Subtype.ext
  funext j
  rw [originalL2MeanZeroSource_apply,complexMeanZeroSobolevInclusion_val,WeightedCoeff.sobolevInclusion_apply]

def originalL2MeanZeroDomain (D : GlobalRoughAbelianForwardData) :
    Set (complexMeanZeroWeightedSubmodule (Weight.sobolev 0)) :=
  (complexMeanZeroSobolevInclusion (by norm_num : (-1:ℝ)≤0)) ⁻¹' D.originalMeanZeroDomain

theorem originalL2MeanZeroDomain_open (D : GlobalRoughAbelianForwardData) : IsOpen D.originalL2MeanZeroDomain :=
  D.originalMeanZeroDomain_open.preimage (complexMeanZeroSobolevInclusion (by norm_num : (-1:ℝ)≤0)).continuous

theorem originalL2MeanZero_mem_domain (D : GlobalRoughAbelianForwardData)
    (q : complexMeanZeroWeightedSubmodule (Weight.sobolev 0))
    (hr : IsRealPeriodOneHminusOne (originalL2MeanZeroSource q)) :
    q∈D.originalL2MeanZeroDomain := by
  change (complexMeanZeroSobolevInclusion (by norm_num : (-1:ℝ)≤0) q).val∈D.canonicalDomain
  rw [←originalL2MeanZeroSource_eq_intrinsic]
  exact D.real_meanZero_mem_canonicalDomain _ hr (originalL2MeanZeroSource_zero_coefficient q)

theorem exists_original_l2_domain_refinement (D : GlobalRoughAbelianForwardData)
    (U : Set (complexMeanZeroWeightedSubmodule (Weight.sobolev 0))) (hU : IsOpen U)
    (hreal : ∀ q,IsRealPeriodOneHminusOne (originalL2MeanZeroSource q) → q∈U) :
    ∃ V : Set (complexMeanZeroWeightedSubmodule (Weight.sobolev 0)),IsOpen V ∧
      (∀ q,IsRealPeriodOneHminusOne (originalL2MeanZeroSource q) → q∈V) ∧ V⊆U ∧
      V⊆D.originalL2MeanZeroDomain := by
  exact NLS.ComplexAnalysis.exists_restricted_real_neighborhood
    (fun q => IsRealPeriodOneHminusOne (originalL2MeanZeroSource q))
    D.originalL2MeanZeroDomain D.originalL2MeanZeroDomain_open D.originalL2MeanZero_mem_domain U hU hreal

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
