import NLS.SequenceSpaces.PhysicalRealSobolevInclusion
import NLS.SequenceSpaces.CompactSobolevInclusion

/-! Strict Sobolev inclusion is compact in the exact normalized physical
real mean-zero norms, with no change of Fourier coordinates. -/
noncomputable section
namespace NLS

theorem isCompactOperator_physicalRealSobolevInclusion {s t : ℝ} (h : t<s) :
    IsCompactOperator (physicalRealSobolevInclusion h.le) := by
  have hc : IsCompactOperator (WeightedCoeff.meanZeroSobolevInclusion h.le) :=
    ((WeightedCoeff.isCompactOperator_sobolevInclusion_strict h).comp_clm
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev s))).clm_comp
      (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev t))
  have hr : IsCompactOperator ((WeightedCoeff.meanZeroSobolevInclusion h.le).restrictScalars ℝ) := hc
  exact (hr.comp_clm physicalRealDeletedSubmodule.subtypeL).codRestrict
    (meanZeroSobolevInclusion_physical_real h.le) isClosed_physicalRealDeletedSubmodule

end NLS
