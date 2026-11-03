import NLS.MKdV.MiuraCartesianSobolevInverse
import NLS.MKdV.MiuraSobolevPhaseSaturation

/-! # Physical actions and signed mean determine the original NLS actions

Global Cartesian injectivity removes the former ambiguity between distinct
original NLS action fibers. Phase saturation supplies the comparison point
with the same full Cartesian data and the prescribed original NLS actions.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- At arbitrary native integer H^s profiles, s>=1, equality of physical
mKdV actions and signed mean implies equality of the whole original signed
NLS action sequence. No open-gap or finite-gap restriction is imposed. -/
theorem miuraOriginalNLSActions_eq_of_Sobolev_actionMean_eq (s : ℕ) (hs : 1 ≤ s)
    (a b : MiuraRealSobolevSource s)
    (hJ : miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s a) =
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s b)) :
    miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s a).val =
      miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s b).val := by
  have hcoord := congrArg Subtype.val (miuraPhysicalSobolevCartesianMap_L2 s b)
  change miuraPositiveSobolevL2CartesianInclusion s (miuraPhysicalSobolevCartesianMap s b).val =
    (miuraPhysicalCartesianMap (miuraPhysicalSobolevL2SourceInclusion s b)).val at hcoord
  rw [miuraPhysicalCartesianMap_inclusion] at hcoord
  have hrad : miuraPositiveCartesianActionMean
      (miuraPositiveSobolevL2CartesianInclusion s (miuraPhysicalSobolevCartesianMap s b).val) =
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s a) := by
    rw [hcoord,miuraPositiveCartesianActionMean_map _ (miuraPhysicalSobolevL2SourceInclusion s b).property]
    exact hJ.symm
  obtain ⟨B,hB,hI⟩ := exists_miuraSobolev_Cartesian_phase_preimage s a
    (miuraPhysicalSobolevCartesianMap s b) hrad
  have he := miuraPhysicalSobolevCartesianMap_injective s hs hB
  subst B
  exact hI.symm

end NLS.MKdV
