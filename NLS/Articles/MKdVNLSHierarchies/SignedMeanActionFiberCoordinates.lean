import NLS.MKdV.MiuraSobolevJointFiberFaithfulness

/-! # Faithful Cartesian phase coordinates at arbitrary signed mean

The signed mean removes the central NLS half-turn ambiguity. Each fixed
NLS-action and signed-mean branch has its full native Cartesian phase
fiber as a homeomorphic image, with unique phase lifts in every native
integer Sobolev class. Comparison of different NLS action fibers at the
same physical J and mean remains a separate obligation.
-/
noncomputable section
open Set Complex NLS.MKdV
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- The actual central NLS half turn reverses the literal signed mean,
globally on the physical original-L2 diagonal. -/
theorem physical_central_halfTurn_reverses_signed_mean (a : MiuraRealL2) :
    (miuraCentralHalfTurn a).val 0 = -a.val 0 := miuraCentralHalfTurn_mean a

/-- No central ambiguity remains for equal actual Cartesian maps on a
fixed original NLS action fiber, at any signed mean. -/
theorem physical_Cartesian_NLS_action_fiber_injective (a b : MiuraRealL2)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val)
    (hM : miuraPositiveCartesianMap a.val = miuraPositiveCartesianMap b.val) : b = a :=
  miuraCartesian_jointFiber_injective a b hI hM

theorem physical_joint_fiber_signed_mean_branch (a : MiuraRealL2) :
    miuraJointActionFiber a = {b | miuraOriginalNLSActionSequence b.val = miuraOriginalNLSActionSequence a.val ∧
      b.val 0 = a.val 0} := miuraJointActionFiber_eq_signedMean_NLSActionFiber a

/-- Exact global topological phase coordinates on every compact signed
mean branch of an original NLS action fiber. -/
theorem physical_action_fiber_Cartesian_homeomorphism (a : MiuraRealL2) :
    ∃ H : miuraJointActionFiber a ≃ₜ miuraCartesianPhaseFiber a,
      ∀ b : miuraJointActionFiber a, (H b).val = miuraPositiveCartesianMap b.val.val :=
  ⟨miuraJointFiberCartesianHomeomorph a,miuraJointFiberCartesianHomeomorph_apply a⟩

theorem physical_action_fiber_unique_phase_lift (a : MiuraRealL2)
    (z : MiuraPositiveCartesianTarget) (hz : z ∈ miuraCartesianRealSubmodule)
    (hJ : miuraPositiveCartesianActionMean z = miuraRealL2ActionMeanMap a) :
    ∃! b : MiuraRealL2, miuraPositiveCartesianMap b.val = z ∧
      miuraOriginalNLSActionSequence b.val = miuraOriginalNLSActionSequence a.val := by
  obtain ⟨b,hb,hMb⟩ := exists_miura_jointFiber_preimage_of_Cartesian_radii a z hz hJ
  refine ⟨b,⟨hMb,hb.2⟩,?_⟩
  intro c hc
  exact miuraCartesian_jointFiber_injective b c (hb.2.trans hc.2.symm) (hMb.trans hc.1.symm)

/-- Every attained native phase configuration has exactly one preimage
within the prescribed original NLS action fiber in the same H^s class. -/
theorem physical_action_fiber_unique_phase_lift_allSobolev (s : ℕ) (a : MiuraRealSobolevSource s)
    (z : MiuraRealSobolevCartesianTarget s)
    (hJ : miuraPositiveCartesianActionMean (miuraPositiveSobolevL2CartesianInclusion s z.val) =
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s a)) :
    ∃! b : MiuraRealSobolevSource s, miuraPhysicalSobolevCartesianMap s b = z ∧
      miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s b).val =
        miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s a).val :=
  existsUnique_miuraSobolev_phase_preimage s a z hJ

/-- The source's printed global recovery of the signed mean from NLS
actions alone is impossible even for an arbitrary, nonanalytic factor. -/
theorem no_global_signed_mean_NLS_action_factor :
    ¬∃ F : Coeff 1 → ℂ, ∀ a : MiuraRealL2, F (miuraOriginalNLSActionSequence a.val) = a.val 0 := by
  rintro ⟨F,hF⟩
  have h := hF (miuraCentralHalfTurn (miuraRealConstant 1))
  rw [miuraCentralHalfTurn_NLS_actionSequence,hF (miuraRealConstant 1),
    miuraCentralHalfTurn_mean,miuraRealConstant_mean] at h
  norm_num at h

end NLS.Articles.MKdVNLSHierarchies
