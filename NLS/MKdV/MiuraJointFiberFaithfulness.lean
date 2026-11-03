import NLS.MKdV.MiuraCentralHalfTurnMean
import NLS.MKdV.MiuraZeroMeanJointFiberHomeomorph

/-! # Faithful Cartesian phase coordinates at every signed mean

The central half turn reverses the signed mean. Equality of the actual
Cartesian/mean maps therefore removes its ambiguity on every original
NLS action fiber, including zero mean. Different NLS action fibers at the
same physical J and mean are not identified here.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraRealDiagonalL2Source_injective : Function.Injective miuraRealDiagonalL2Source := by
  intro a b h
  apply Subtype.ext
  have he := congrArg (fun φ : ZakharovShabat.realTypeSourceSubmodule 2 => φ.val.fst) h
  change (scalarL2Diagonal a.val).fst = (scalarL2Diagonal b.val).fst at he
  simpa only [scalarL2Diagonal_fst] using he

/-- Global Cartesian faithfulness within every original signed NLS
action fiber. The literal signed mean removes the central half turn. -/
theorem miuraCartesian_jointFiber_injective (a b : MiuraRealL2)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val)
    (hM : miuraPositiveCartesianMap a.val = miuraPositiveCartesianMap b.val) : b = a := by
  rcases miuraCartesian_jointFiber_eq_or_central_halfTurn a b hI hM with h | h
  · exact miuraRealDiagonalL2Source_injective h
  · have hb : b = miuraCentralHalfTurn a := miuraRealDiagonalL2Source_injective
      (h.trans (miuraCentralHalfTurn_source a).symm)
    have hmean := congrArg Prod.snd hM
    change a.val 0 = b.val 0 at hmean
    rw [hb,miuraCentralHalfTurn_mean] at hmean
    have hm : a.val 0 = 0 := by linear_combination (1/2 : ℂ)*hmean
    exact miuraCartesian_jointFiber_injective_of_mean_zero a b hm hI hM

theorem miuraJointFiberCartesianMap_injective (a : MiuraRealL2) : Function.Injective (miuraJointFiberCartesianMap a) := by
  intro x y h
  have hI : miuraOriginalNLSActionSequence x.val.val = miuraOriginalNLSActionSequence y.val.val :=
    x.property.2.trans y.property.2.symm
  have hM : miuraPositiveCartesianMap x.val.val = miuraPositiveCartesianMap y.val.val := congrArg Subtype.val h
  apply Subtype.ext
  exact (miuraCartesian_jointFiber_injective x.val y.val hI hM).symm

/-- Every compact joint action fiber has its full native Cartesian phase
fiber as a genuine homeomorphic image, at any signed mean. -/
def miuraJointFiberCartesianHomeomorph (a : MiuraRealL2) : miuraJointActionFiber a ≃ₜ miuraCartesianPhaseFiber a := by
  letI : CompactSpace (miuraJointActionFiber a) := isCompact_iff_compactSpace.mp (isCompact_miuraJointActionFiber a)
  let e := Equiv.ofBijective (miuraJointFiberCartesianMap a)
    ⟨miuraJointFiberCartesianMap_injective a,miuraJointFiberCartesianMap_surjective a⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := e) (continuous_miuraJointFiberCartesianMap a)

@[simp] theorem miuraJointFiberCartesianHomeomorph_apply (a : MiuraRealL2) (b : miuraJointActionFiber a) :
    (miuraJointFiberCartesianHomeomorph a b).val = miuraPositiveCartesianMap b.val.val := rfl

/-- At any mean, the joint fiber is the complete physical diagonal NLS
action fiber restricted to the same literal signed mean. -/
theorem miuraJointActionFiber_eq_signedMean_NLSActionFiber (a : MiuraRealL2) :
    miuraJointActionFiber a = {b | miuraOriginalNLSActionSequence b.val = miuraOriginalNLSActionSequence a.val ∧
      b.val 0 = a.val 0} := by
  ext b
  constructor
  · intro hb
    exact ⟨hb.2,congrArg (fun z : MiuraActionMeanTarget => z.2) hb.1⟩
  · rintro ⟨hI,hm⟩
    exact ⟨Prod.ext (miuraL2ActionSequence_eq_of_NLS_actions_eq b a hI) hm,hI⟩

end NLS.MKdV
