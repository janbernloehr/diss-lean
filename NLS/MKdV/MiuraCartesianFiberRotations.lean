import NLS.MKdV.MiuraCartesianActionParameters
import NLS.MKdV.MiuraNLSActionsCartesianChart
import NLS.SequenceSpaces.PositiveCartesianRealRotations

/-! # Conserved compact fibers and real normalized Cartesian rotations -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraRealL2ActionRotation (a : MiuraRealL2) (n : ℕ) (t : ℝ) : MiuraRealL2 :=
  ⟨miuraOriginalL2ActionFlow a.val a.property n t,miuraOriginalL2ActionFlow_real a.val a.property n t⟩

def miuraRealCartesianParameters (a : MiuraRealL2) : RealCoeff 2 × RealCoeff 2 :=
  WeightedCoeff.positiveCartesianRealParameters (Weight.sobolev (1/2)) 2 (miuraPositiveCartesianMap a.val)

theorem continuous_miuraRealCartesianParameters : Continuous miuraRealCartesianParameters :=
  (WeightedCoeff.positiveCartesianRealParameters (Weight.sobolev (1/2)) 2).continuous.comp
    continuous_miuraRealPositiveCartesianMap

theorem continuous_miuraRealOriginalNLSActionSequence :
    Continuous (fun a : MiuraRealL2 => miuraOriginalNLSActionSequence a.val) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact (analyticOnNhd_miuraOriginalNLSActionSequence a.val
    (real_mem_miuraOriginalNLSActionDomain a.val a.property)).continuousAt.comp
      continuous_subtype_val.continuousAt

/-- The whole native action/mean map is invariant under each native
Cartesian rotation, at every complex target. -/
theorem miuraPositiveCartesianActionMean_rotation (z : MiuraPositiveCartesianTarget)
    (n : ℕ) (t : ℝ) :
    miuraPositiveCartesianActionMean (miuraCartesianRotation n t z) = miuraPositiveCartesianActionMean z := by
  apply Prod.ext
  · apply Subtype.ext
    funext k
    simp only [miuraPositiveCartesianActionMean,miuraL2CartesianActions_apply]
    have he := miuraCartesianRotation_eval n k t z
    by_cases hk : k = n
    · rw [if_pos hk] at he
      have hrad := congrArg (fun b : ℂ × ℂ => b.1^2+b.2^2) he
      rw [cartesianPlaneRotation_radius] at hrad
      exact congrArg (fun r : ℂ => (1/2 : ℂ)*r) hrad
    · rw [if_neg hk] at he
      exact congrArg (fun b : ℂ × ℂ => (1/2 : ℂ)*(b.1^2+b.2^2)) he
  · exact miuraCartesianRotation_mean n t z

theorem miuraRealL2ActionRotation_actionMean (a : MiuraRealL2) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    miuraRealL2ActionMeanMap (miuraRealL2ActionRotation a n t) = miuraRealL2ActionMeanMap a := by
  change miuraL2ActionMeanMap (miuraRealL2ActionRotation a n t).val = miuraL2ActionMeanMap a.val
  rw [← miuraPositiveCartesianActionMean_map (miuraRealL2ActionRotation a n t).val
    (miuraRealL2ActionRotation a n t).property,← miuraPositiveCartesianActionMean_map a.val a.property]
  change miuraPositiveCartesianActionMean (miuraPositiveCartesianMap (miuraOriginalL2ActionFlow a.val a.property n t)) = _
  rw [miuraPositiveCartesianMap_originalActionFlow a.val a.property n hn t,
    miuraPositiveCartesianActionMean_rotation]

theorem miuraRealCartesianParameters_actionRotation (a : MiuraRealL2) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    miuraRealCartesianParameters (miuraRealL2ActionRotation a n t) =
      RealCoeff.actionRotation (miuraRealCartesianParameters a) n (-t) := by
  change WeightedCoeff.positiveCartesianRealParameters (Weight.sobolev (1/2)) 2
    (miuraPositiveCartesianMap (miuraOriginalL2ActionFlow a.val a.property n t)) = _
  rw [miuraPositiveCartesianMap_originalActionFlow a.val a.property n hn t]
  exact WeightedCoeff.positiveCartesianRealParameters_rotation (Weight.sobolev (1/2)) 2 _ n (by omega) t

/-- A compact global fiber fixing physical actions, signed mean, and the
entire original signed NLS action sequence. -/
def miuraJointActionFiber (a : MiuraRealL2) : Set MiuraRealL2 :=
  {b | miuraRealL2ActionMeanMap b = miuraRealL2ActionMeanMap a ∧
    miuraOriginalNLSActionSequence b.val = miuraOriginalNLSActionSequence a.val}

theorem isCompact_miuraJointActionFiber (a : MiuraRealL2) : IsCompact (miuraJointActionFiber a) := by
  exact (isCompact_miuraRealL2ActionMeanFiber (miuraRealL2ActionMeanMap a)).inter_right
    (isClosed_eq continuous_miuraRealOriginalNLSActionSequence continuous_const)

theorem miuraRealL2ActionRotation_mem_jointFiber (a b : MiuraRealL2)
    (hb : b ∈ miuraJointActionFiber a) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    miuraRealL2ActionRotation b n t ∈ miuraJointActionFiber a := by
  refine ⟨(miuraRealL2ActionRotation_actionMean b n hn t).trans hb.1,?_⟩
  exact (miuraOriginalNLSActionSequence_actionFlow b.val b.property n t).trans hb.2

end NLS.MKdV
