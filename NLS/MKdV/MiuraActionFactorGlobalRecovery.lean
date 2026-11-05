import NLS.MKdV.MiuraCartesianRealActionLifts
import NLS.MKdV.MiuraGeneralLocalNLSActionFactor
import NLS.MKdV.MiuraCartesianSobolevInverse

/-! # Local analytic factors recover every H1 representative of their data

Nearby real Cartesian lifts, global phase saturation and the unique
entire-L2 preimage of native data remove the source-neighborhood restriction.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraPhysicalCartesian_fiber_unique_of_Sobolev (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (b : MiuraRealL2)
    (hb : miuraPhysicalCartesianMap b = miuraPhysicalCartesianMap (miuraPhysicalSobolevL2SourceInclusion s a)) :
    b = miuraPhysicalSobolevL2SourceInclusion s a := by
  obtain ⟨c,_,hu⟩ := existsUnique_miuraPhysicalCartesian_preimage_Sobolev s hs (miuraPhysicalSobolevCartesianMap s a)
  have ha := (miuraPhysicalSobolevCartesianMap_L2 s a).symm
  exact (hu b (hb.trans ha)).trans (hu _ ha).symm

namespace MiuraGeneralCartesianNLSActionChart
variable {a : MiuraRealL2}

/-- A physical chart value with native H1 action data equals the original
NLS actions of every H1 profile carrying those physical actions and mean. -/
theorem observables_eq_of_H1_actionMean (C : MiuraGeneralCartesianNLSActionChart a)
    (b : MiuraRealSobolevSource 1) (z : MiuraPositiveCartesianTarget)
    (hz : z ∈ Metric.ball (miuraPositiveCartesianMap a.val) C.radius)
    (hzr : z ∈ miuraCartesianRealSubmodule)
    (hJ : miuraPositiveCartesianActionMean z = miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 b)) :
    C.observables z = miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion 1 b).val := by
  let b₀ := miuraPhysicalSobolevL2SourceInclusion 1 b
  obtain ⟨c,hc,hMc⟩ := exists_miura_jointFiber_preimage_of_Cartesian_radii b₀ z hzr hJ
  obtain ⟨B,hB⟩ := exists_miuraJointFiber_Sobolev_representative 1 b c hc.2
  let p : MiuraRealL2 := ⟨C.inverse z,C.inverse_real z hz hzr⟩
  have hpc : miuraPhysicalCartesianMap p = miuraPhysicalCartesianMap c := by
    apply Subtype.ext
    rw [miuraPhysicalCartesianMap_inclusion,miuraPhysicalCartesianMap_inclusion]
    change miuraPositiveCartesianMap (C.inverse z) = miuraPositiveCartesianMap c.val
    rw [(C.right_inverse z hz).2,hMc]
  have hp : p = c :=
    (miuraPhysicalCartesian_fiber_unique_of_Sobolev 1 le_rfl B p
      (hpc.trans (congrArg miuraPhysicalCartesianMap hB.symm))).trans hB
  change miuraOriginalNLSActionSequence p.val = miuraOriginalNLSActionSequence b₀.val
  rw [hp]
  exact hc.2

/-- Local action factors have global H1 recovery on an open action
neighborhood: the representative need not be near the chart's basepoint. -/
theorem exists_action_factor_global_H1_recovery (C : MiuraGeneralCartesianNLSActionChart a) :
    ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen V ∧ miuraRealL2ActionMeanMap a ∈ V ∧ AnalyticOnNhd ℂ F V ∧
        ∀ b : MiuraRealSobolevSource 1,
          miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 b) ∈ V →
          F (miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 b)) =
            miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion 1 b).val := by
  obtain ⟨W,V₀,F,hW,haW,hWball,hV₀,haV₀,hF,hrec⟩ := C.exists_native_action_factor
  let z : MiuraRealCartesianTarget := ⟨miuraPositiveCartesianMap a.val,miuraPositiveCartesianMap_physicalReal a⟩
  obtain ⟨V₁,hV₁,haV₁,hlift⟩ := exists_miuraCartesian_real_action_lift_neighborhood z W hW haW
  have he : miuraPositiveCartesianActionMean (miuraPositiveCartesianMap a.val) = miuraRealL2ActionMeanMap a :=
    miuraPositiveCartesianActionMean_map a.val a.property
  refine ⟨V₀ ∩ V₁,F,hV₀.inter hV₁,?_,hF.mono inter_subset_left,?_⟩
  · exact ⟨he ▸ haV₀,he ▸ haV₁⟩
  · intro b hb
    obtain ⟨v,hv,hvr,hJ⟩ := hlift (miuraPhysicalSobolevL2SourceInclusion 1 b) hb.2
    have hf := (hrec v hv).2
    rw [hJ] at hf
    exact hf.trans (C.observables_eq_of_H1_actionMean b v (hWball hv) hvr hJ)

end MiuraGeneralCartesianNLSActionChart

theorem exists_miura_action_factor_global_H1_recovery_at_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen V ∧ miuraL2ActionMeanMap (scalarInclusion a) ∈ V ∧ AnalyticOnNhd ℂ F V ∧
        ∀ b : MiuraRealSobolevSource 1,
          miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 b) ∈ V →
          F (miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 b)) =
            miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion 1 b).val := by
  obtain ⟨C⟩ := nonempty_miuraGeneralCartesianNLSActionChart a ha
  exact C.exists_action_factor_global_H1_recovery

end NLS.MKdV
