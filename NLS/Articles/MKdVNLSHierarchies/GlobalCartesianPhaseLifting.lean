import NLS.MKdV.MiuraSobolevPhaseSaturation

/-! # Global realization of all phases at attained physical actions

The compact joint physical/NLS action fiber maps onto the complete native
Cartesian phase fiber. Every simultaneous phase configuration is realized
in the initial profile's Sobolev class, preserving all original NLS
actions and the signed mean. The result includes closed gaps, zero mean,
and infinitely many open modes. It does not assert global injectivity or
surjectivity onto action sequences that have not yet been attained.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- Global original-L2 phase lifting, retaining all actual original signed
NLS actions, the entire native physical action sequence, and signed mean. -/
theorem physical_Cartesian_phase_lifting_original_L2 (a : MiuraRealL2)
    (z : MiuraPositiveCartesianTarget) (hz : z ∈ miuraCartesianRealSubmodule)
    (hJ : miuraPositiveCartesianActionMean z = miuraRealL2ActionMeanMap a) :
    ∃ b : MiuraRealL2, miuraPositiveCartesianMap b.val = z ∧
      miuraRealL2ActionMeanMap b = miuraRealL2ActionMeanMap a ∧
      ∀ k : ℤ, sourceComplexAction (by simp) (by norm_num) k (scalarL2Diagonal b.val) =
        sourceComplexAction (by simp) (by norm_num) k (scalarL2Diagonal a.val) := by
  obtain ⟨b,hb,hM⟩ := exists_miura_jointFiber_preimage_of_Cartesian_radii a z hz hJ
  refine ⟨b,hM,hb.1,fun k => ?_⟩
  have h := congrArg (fun c : Coeff 1 => c k) hb.2
  simpa only [miuraOriginalNLSActionSequence_apply _ (real_mem_miuraOriginalNLSActionDomain _ b.property),
    miuraOriginalNLSActionSequence_apply _ (real_mem_miuraOriginalNLSActionDomain _ a.property)] using h

/-- The complete native Cartesian phase fiber is the exact image of a
compact physical fiber fixing every original signed NLS action. -/
theorem physical_Cartesian_phase_fiber_exact_image (a : MiuraRealL2) :
    IsCompact (miuraJointActionFiber a) ∧
      miuraRealPositiveCartesianMap '' miuraJointActionFiber a = miuraCartesianPhaseFiber a ∧
      IsCompact (miuraCartesianPhaseFiber a) :=
  ⟨isCompact_miuraJointActionFiber a,miuraJointActionFiber_Cartesian_image a,isCompact_miuraCartesianPhaseFiber a⟩

/-- Actual original NLS actions determine all nonnegative real Sobolev
regularities on the physical diagonal, without a smallness restriction. -/
theorem physical_NLS_action_fiber_Sobolev_regularity (a b : MiuraRealL2)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val)
    (t : ℝ) (ht : 0 ≤ t) :
    Memℓp (fun n : ℤ => (Weight.sobolev t n : ℂ)*a.val n) 2 ↔
      Memℓp (fun n : ℤ => (Weight.sobolev t n : ℂ)*b.val n) 2 :=
  miuraSobolev_mem_iff_of_NLS_actions_eq a b hI t ht

/-- Global phase lifting in each actual native integer H^s space, with
every original signed NLS action preserved. -/
theorem physical_Cartesian_phase_lifting_allSobolev (s : ℕ) (a : MiuraRealSobolevSource s)
    (z : MiuraRealSobolevCartesianTarget s)
    (hJ : miuraPositiveCartesianActionMean (miuraPositiveSobolevL2CartesianInclusion s z.val) =
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s a)) :
    ∃ b : MiuraRealSobolevSource s, miuraPhysicalSobolevCartesianMap s b = z ∧
      ∀ k : ℤ, sourceComplexAction (by simp) (by norm_num) k
        (scalarL2Diagonal (miuraPhysicalSobolevL2SourceInclusion s b).val) =
        sourceComplexAction (by simp) (by norm_num) k
          (scalarL2Diagonal (miuraPhysicalSobolevL2SourceInclusion s a).val) := by
  obtain ⟨b,hM,hI⟩ := exists_miuraSobolev_Cartesian_phase_preimage s a z hJ
  refine ⟨b,hM,fun k => ?_⟩
  have h := congrArg (fun c : Coeff 1 => c k) hI
  simpa only [miuraOriginalNLSActionSequence_apply _
      (real_mem_miuraOriginalNLSActionDomain _ (miuraPhysicalSobolevL2SourceInclusion s b).property),
    miuraOriginalNLSActionSequence_apply _
      (real_mem_miuraOriginalNLSActionDomain _ (miuraPhysicalSobolevL2SourceInclusion s a).property)] using h

end NLS.Articles.MKdVNLSHierarchies
