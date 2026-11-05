import NLS.MKdV.MiuraJointFiberSobolevRegularity

/-! # Global phase lifting at every native integer Sobolev order -/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraPositiveSobolevL2CartesianInclusion_injective (s : ℕ) :
    Function.Injective (miuraPositiveSobolevL2CartesianInclusion s) := by
  intro z v he
  apply WeightedCoeff.positivePairMean_ext (w := miuraCartesianWeight s) (p := 2)
  · intro n _hn
    change miuraSobolevPositiveEval s n z = miuraSobolevPositiveEval s n v
    have h := congrArg (miuraPositiveCartesianEval n) he
    simpa only [miuraPositiveSobolevL2CartesianInclusion_eval] using h
  · have h := congrArg Prod.snd he
    simpa only [miuraPositiveSobolevL2CartesianInclusion_mean] using h

/-- Every complete native phase configuration at attained actions and
signed mean lifts globally in the same H^s space. Every original signed
NLS action is preserved. No smallness or open-gap hypothesis is needed. -/
theorem exists_miuraSobolev_Cartesian_phase_preimage (s : ℕ) (a : MiuraRealSobolevSource s)
    (z : MiuraRealSobolevCartesianTarget s)
    (hJ : miuraPositiveCartesianActionMean (miuraPositiveSobolevL2CartesianInclusion s z.val) =
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s a)) :
    ∃ b : MiuraRealSobolevSource s, miuraPhysicalSobolevCartesianMap s b = z ∧
      miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s b).val =
        miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s a).val := by
  obtain ⟨b,hb,hM⟩ := exists_miura_jointFiber_preimage_of_Cartesian_radii
    (miuraPhysicalSobolevL2SourceInclusion s a) (miuraPositiveSobolevL2CartesianInclusion s z.val)
    (miuraPositiveSobolevL2CartesianInclusion_real s z) hJ
  obtain ⟨B,hB⟩ := exists_miuraJointFiber_Sobolev_representative s a b hb.2
  refine ⟨B,?_,by simpa only [hB] using hb.2⟩
  apply Subtype.ext
  apply miuraPositiveSobolevL2CartesianInclusion_injective s
  have h := congrArg Subtype.val (miuraPhysicalSobolevCartesianMap_L2 s B)
  change miuraPositiveSobolevL2CartesianInclusion s (miuraPhysicalSobolevCartesianMap s B).val =
    (miuraPhysicalCartesianMap (miuraPhysicalSobolevL2SourceInclusion s B)).val at h
  rw [h,miuraPhysicalCartesianMap_inclusion,hB,hM]

end NLS.MKdV
