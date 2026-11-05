import NLS.MKdV.MiuraJointFiberNLSCoordinates
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Exact Cartesian phase coordinates on zero-mean joint action fibers

The compact fiber fixing all original NLS actions, physical actions and
zero signed mean maps homeomorphically onto its complete Cartesian phase
fiber. This does not identify different NLS action fibers at the same J.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraJointFiberCartesianMap (a : MiuraRealL2) :
    miuraJointActionFiber a → miuraCartesianPhaseFiber a := fun b =>
  ⟨miuraRealPositiveCartesianMap b.val,miuraPositiveCartesianMap_physicalReal b.val,
    (miuraPositiveCartesianActionMean_map b.val.val b.val.property).trans b.property.1⟩

theorem continuous_miuraJointFiberCartesianMap (a : MiuraRealL2) : Continuous (miuraJointFiberCartesianMap a) := by
  exact (continuous_miuraRealPositiveCartesianMap.comp continuous_subtype_val).subtype_mk _

theorem miuraJointFiberCartesianMap_surjective (a : MiuraRealL2) : Function.Surjective (miuraJointFiberCartesianMap a) := by
  intro z
  obtain ⟨b,hb,hM⟩ := exists_miura_jointFiber_preimage_of_Cartesian_radii a z.val z.property.1 z.property.2
  exact ⟨⟨b,hb⟩,Subtype.ext hM⟩

theorem miuraJointFiberCartesianMap_injective_of_mean_zero (a : MiuraRealL2) (hm : a.val 0 = 0) :
    Function.Injective (miuraJointFiberCartesianMap a) := by
  intro x y he
  have hmx : x.val.val 0 = 0 := by
    have h := congrArg (fun z : MiuraActionMeanTarget => z.2) x.property.1
    exact h.trans hm
  have hI : miuraOriginalNLSActionSequence x.val.val = miuraOriginalNLSActionSequence y.val.val :=
    x.property.2.trans y.property.2.symm
  have hM : miuraPositiveCartesianMap x.val.val = miuraPositiveCartesianMap y.val.val := congrArg Subtype.val he
  apply Subtype.ext
  exact (miuraCartesian_jointFiber_injective_of_mean_zero x.val y.val hmx hI hM).symm

/-- A genuine homeomorphism on each zero-mean joint action fiber, using
the original L2 topology and the full native Cartesian target topology. -/
def miuraZeroMeanJointFiberCartesianHomeomorph (a : MiuraRealL2) (hm : a.val 0 = 0) :
    miuraJointActionFiber a ≃ₜ miuraCartesianPhaseFiber a := by
  letI : CompactSpace (miuraJointActionFiber a) := isCompact_iff_compactSpace.mp (isCompact_miuraJointActionFiber a)
  let e := Equiv.ofBijective (miuraJointFiberCartesianMap a)
    ⟨miuraJointFiberCartesianMap_injective_of_mean_zero a hm,miuraJointFiberCartesianMap_surjective a⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := e) (continuous_miuraJointFiberCartesianMap a)

@[simp] theorem miuraZeroMeanJointFiberCartesianHomeomorph_apply (a : MiuraRealL2) (hm : a.val 0 = 0)
    (b : miuraJointActionFiber a) :
    (miuraZeroMeanJointFiberCartesianHomeomorph a hm b).val = miuraPositiveCartesianMap b.val.val := rfl

end NLS.MKdV
