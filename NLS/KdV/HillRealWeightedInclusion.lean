import NLS.KdV.HillOriginalWeightedMeanZeroSource

noncomputable section
set_option autoImplicit false
namespace NLS.KdV

/-- A norm-decreasing inclusion that retains the physical period-one coefficients. -/
def hillRealWeightedInclusion (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (p : RealHillWeightedPotential w) : RealHillWeightedPotential v :=
  ⟨WeightedCoeff.inclusionCLM w.doubleIndex.toWeight v.doubleIndex.toWeight
    (fun k => by simpa only [SpectralWeight.toWeight_apply,SpectralWeight.doubleIndex_apply] using h (2*k)) p.val,fun k => by
      simpa only [SpectralWeight.toCoeff_apply,WeightedCoeff.inclusionCLM_apply] using p.property k⟩

@[simp] theorem hillRealWeightedInclusion_apply (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (p : RealHillWeightedPotential w) (k : ℤ) :
    (hillRealWeightedInclusion w v h p).val.val k = p.val.val k :=
  WeightedCoeff.inclusionCLM_apply _ _ _ p.val k

theorem norm_hillRealWeightedInclusion_le (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (p : RealHillWeightedPotential w) : ‖(hillRealWeightedInclusion w v h p).val‖ ≤ ‖p.val‖ :=
  WeightedCoeff.norm_inclusionCLM_le _ _ _ p.val

theorem hillOriginalWeightedMeanZeroSource_inclusion (w v : SpectralWeight)
    (h : ∀ k, v k ≤ w k) (p : RealHillWeightedPotential w) (hmean : p.val.val 0 = 0) :
    hillOriginalWeightedMeanZeroSource v (hillRealWeightedInclusion w v h p)
        (by simpa only [hillRealWeightedInclusion_apply] using hmean) =
      hillOriginalWeightedMeanZeroSource w p hmean := by
  apply Subtype.ext
  apply Subtype.ext
  exact hillPeriodOneUnitPotential_eq_of_coeff_eq v w _ _
    (fun k => hillRealWeightedInclusion_apply w v h p k)

end NLS.KdV
