import NLS.MKdV.MiuraZeroMeanJointFiberHomeomorph
import NLS.MKdV.MiuraNLSActionFiberMean
import NLS.MKdV.MiuraZeroMeanSobolevFaithfulness

/-! # Faithful global phase coordinates on zero-mean NLS action fibers

Every zero-mean physical diagonal NLS action fiber is exactly a joint
physical/NLS action fiber and maps homeomorphically onto the complete
native Cartesian phase fiber. At general mean only the central NLS
half-turn can remain on a fixed NLS action fiber. This does not identify
different NLS action fibers having the same physical J sequence.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- Positive original NLS coordinates on the physical diagonal leave at
most one central half-turn ambiguity on an original NLS action fiber. -/
theorem physical_Cartesian_NLS_action_fiber_central_ambiguity (a b : MiuraRealL2)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val)
    (hM : miuraPositiveCartesianMap a.val = miuraPositiveCartesianMap b.val) :
    miuraRealDiagonalL2Source b = miuraRealDiagonalL2Source a ∨
      miuraRealDiagonalL2Source b = miuraActionFlowFamily.data.hilbertActionRotation
        (miuraRealDiagonalL2Source a) 0 Real.pi :=
  miuraCartesian_jointFiber_eq_or_central_halfTurn a b hI hM

/-- Global injectivity on the actual original NLS action fiber at zero
mean, without smallness, finite-gap or open-action restrictions. -/
theorem physical_Cartesian_zero_mean_NLS_action_fiber_injective (a b : MiuraRealL2)
    (hm : a.val 0 = 0)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val)
    (hM : miuraPositiveCartesianMap a.val = miuraPositiveCartesianMap b.val) : b = a :=
  miuraCartesian_jointFiber_injective_of_mean_zero a b hm hI hM

/-- The complete physical diagonal original-NLS-action fiber at zero
mean is the compact joint physical-action/mean and NLS-action fiber. -/
theorem physical_zero_mean_NLS_action_fiber_identification (a : MiuraRealL2) (hm : a.val 0 = 0) :
    miuraJointActionFiber a = {b | miuraOriginalNLSActionSequence b.val = miuraOriginalNLSActionSequence a.val} :=
  miuraJointActionFiber_eq_NLSActionFiber_of_mean_zero a hm

/-- A genuine global homeomorphism on the compact zero-mean action
fiber, retaining the original source and complete native target norms. -/
theorem physical_zero_mean_action_fiber_Cartesian_homeomorphism (a : MiuraRealL2) (hm : a.val 0 = 0) :
    ∃ H : miuraJointActionFiber a ≃ₜ miuraCartesianPhaseFiber a,
      ∀ b : miuraJointActionFiber a, (H b).val = miuraPositiveCartesianMap b.val.val :=
  ⟨miuraZeroMeanJointFiberCartesianHomeomorph a hm,miuraZeroMeanJointFiberCartesianHomeomorph_apply a hm⟩

/-- Every complete phase configuration at attained zero-mean actions
has exactly one preimage in the original physical NLS action fiber. -/
theorem physical_zero_mean_action_fiber_unique_phase_lift (a : MiuraRealL2) (hm : a.val 0 = 0)
    (z : MiuraPositiveCartesianTarget) (hz : z ∈ miuraCartesianRealSubmodule)
    (hJ : miuraPositiveCartesianActionMean z = miuraRealL2ActionMeanMap a) :
    ∃! b : MiuraRealL2, miuraPositiveCartesianMap b.val = z ∧
      miuraOriginalNLSActionSequence b.val = miuraOriginalNLSActionSequence a.val := by
  obtain ⟨b,hb,hMb⟩ := exists_miura_jointFiber_preimage_of_Cartesian_radii a z hz hJ
  refine ⟨b,⟨hMb,hb.2⟩,?_⟩
  intro c hc
  have hmc := miuraMean_zero_of_NLS_actions_eq a b hm hb.2.symm
  exact miuraCartesian_jointFiber_injective_of_mean_zero b c hmc (hb.2.trans hc.2.symm)
    (hMb.trans hc.1.symm)

/-- The unique zero-mean phase lift lies in the same native integer
Sobolev space, retaining the entire original signed NLS action sequence. -/
theorem physical_zero_mean_action_fiber_unique_phase_lift_allSobolev (s : ℕ)
    (a : MiuraRealSobolevSource s) (hm : a.val.val 0 = 0)
    (z : MiuraRealSobolevCartesianTarget s)
    (hJ : miuraPositiveCartesianActionMean (miuraPositiveSobolevL2CartesianInclusion s z.val) =
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s a)) :
    ∃! b : MiuraRealSobolevSource s, miuraPhysicalSobolevCartesianMap s b = z ∧
      miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s b).val =
        miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s a).val :=
  existsUnique_miuraSobolev_zeroMean_phase_preimage s a hm z hJ

end NLS.Articles.MKdVNLSHierarchies
