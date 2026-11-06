import NLS.MKdV.MiuraJointFiberFaithfulness
import NLS.MKdV.MiuraSobolevPhaseSaturation

/-! # Unique native Sobolev phase lifts at every signed mean -/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraSobolevCartesian_jointFiber_injective (s : ℕ) (a b : MiuraRealSobolevSource s)
    (hI : miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s a).val =
      miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s b).val)
    (hM : miuraPhysicalSobolevCartesianMap s a = miuraPhysicalSobolevCartesianMap s b) : b = a := by
  apply miuraPhysicalSobolevL2SourceInclusion_injective s
  have h := congrArg (miuraPhysicalSobolevL2CartesianInclusion s) hM
  rw [miuraPhysicalSobolevCartesianMap_L2,miuraPhysicalSobolevCartesianMap_L2] at h
  have hraw := congrArg Subtype.val h
  simp only [miuraPhysicalCartesianMap_inclusion] at hraw
  exact miuraCartesian_jointFiber_injective _ _ hI hraw

/-- Every full native phase configuration at attained actions and mean
has exactly one preimage in the prescribed original NLS action fiber. -/
theorem existsUnique_miuraSobolev_phase_preimage (s : ℕ) (a : MiuraRealSobolevSource s)
    (z : MiuraRealSobolevCartesianTarget s)
    (hJ : miuraPositiveCartesianActionMean (miuraPositiveSobolevL2CartesianInclusion s z.val) =
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s a)) :
    ∃! b : MiuraRealSobolevSource s, miuraPhysicalSobolevCartesianMap s b = z ∧
      miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s b).val =
        miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s a).val := by
  obtain ⟨b,hMb,hIb⟩ := exists_miuraSobolev_Cartesian_phase_preimage s a z hJ
  refine ⟨b,⟨hMb,hIb⟩,?_⟩
  intro c hc
  exact miuraSobolevCartesian_jointFiber_injective s b c (hIb.trans hc.2.symm) (hMb.trans hc.1.symm)

end NLS.MKdV
