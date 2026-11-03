import NLS.MKdV.MiuraSobolevPhaseSaturation
import NLS.MKdV.MiuraNLSActionFiberMean

/-! # Unique zero-mean phase lifts in every native integer Sobolev class -/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- Global zero-mean Cartesian faithfulness on a fixed original NLS
action fiber, in every actual native integer H^s source space. -/
theorem miuraSobolevCartesian_jointFiber_injective_of_mean_zero (s : ℕ)
    (a b : MiuraRealSobolevSource s) (hm : a.val.val 0 = 0)
    (hI : miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s a).val =
      miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s b).val)
    (hM : miuraPhysicalSobolevCartesianMap s a = miuraPhysicalSobolevCartesianMap s b) : b = a := by
  apply miuraPhysicalSobolevL2SourceInclusion_injective s
  have hmean : (miuraPhysicalSobolevL2SourceInclusion s a).val 0 = 0 := by
    simpa only [miuraPhysicalSobolevL2SourceInclusion_apply] using hm
  have h := congrArg (miuraPhysicalSobolevL2CartesianInclusion s) hM
  rw [miuraPhysicalSobolevCartesianMap_L2,miuraPhysicalSobolevCartesianMap_L2] at h
  have hraw := congrArg Subtype.val h
  simp only [miuraPhysicalCartesianMap_inclusion] at hraw
  exact miuraCartesian_jointFiber_injective_of_mean_zero _ _ hmean hI hraw

/-- Every phase configuration at attained zero-mean actions has a unique
native H^s preimage in the given original NLS action fiber. -/
theorem existsUnique_miuraSobolev_zeroMean_phase_preimage (s : ℕ)
    (a : MiuraRealSobolevSource s) (hm : a.val.val 0 = 0)
    (z : MiuraRealSobolevCartesianTarget s)
    (hJ : miuraPositiveCartesianActionMean (miuraPositiveSobolevL2CartesianInclusion s z.val) =
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s a)) :
    ∃! b : MiuraRealSobolevSource s, miuraPhysicalSobolevCartesianMap s b = z ∧
      miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s b).val =
        miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s a).val := by
  obtain ⟨b,hMb,hIb⟩ := exists_miuraSobolev_Cartesian_phase_preimage s a z hJ
  have hma : (miuraPhysicalSobolevL2SourceInclusion s a).val 0 = 0 := by
    simpa only [miuraPhysicalSobolevL2SourceInclusion_apply] using hm
  have hmb := miuraMean_zero_of_NLS_actions_eq (miuraPhysicalSobolevL2SourceInclusion s a)
    (miuraPhysicalSobolevL2SourceInclusion s b) hma hIb.symm
  have hmb' : b.val.val 0 = 0 := by simpa only [miuraPhysicalSobolevL2SourceInclusion_apply] using hmb
  refine ⟨b,⟨hMb,hIb⟩,?_⟩
  intro c hc
  exact miuraSobolevCartesian_jointFiber_injective_of_mean_zero s b c hmb'
    (hIb.trans hc.2.symm) (hMb.trans hc.1.symm)

end NLS.MKdV
