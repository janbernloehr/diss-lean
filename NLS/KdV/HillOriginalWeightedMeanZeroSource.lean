import NLS.KdV.HillOriginalBirkhoffMap

noncomputable section
set_option autoImplicit false
namespace NLS.KdV

/-- Forgetting a source weight and inserting its literal even indices
preserves the ORIGINAL physical zero mode. -/
theorem hillRealWeightedEmbedding_zero_mode (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    (hillRealWeightedEmbedding w p).val.val 0 = p.val.val 0 := by
  change (hillPeriodOneUnitPotential w p.val).val 0 = _
  rw [hillPeriodOneUnitPotential,hillForgetWeight_apply,hillPeriodOnePotential_zero]

/-- A weighted physical source, as the SAME original mean-zero Banach
source used by the one fixed global Birkhoff map. -/
def hillOriginalWeightedMeanZeroSource (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (hmean : p.val.val 0 = 0) : hillRealMeanZeroSourceSubmodule :=
  ⟨⟨(hillRealWeightedEmbedding w p).val,(hillRealWeightedEmbedding w p).property⟩,
    (mem_hillRealMeanZeroSourceSubmodule _).mpr ((hillRealWeightedEmbedding_zero_mode w p).trans hmean)⟩

@[simp] theorem hillOriginalWeightedMeanZeroSource_val (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (hmean : p.val.val 0 = 0) :
    (hillOriginalWeightedMeanZeroSource w p hmean).val.val = (hillRealWeightedEmbedding w p).val := rfl

end NLS.KdV
