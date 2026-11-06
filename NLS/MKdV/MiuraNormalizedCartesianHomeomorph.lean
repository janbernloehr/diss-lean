import NLS.MKdV.MiuraSobolevNormalizedActionFlow
import NLS.SequenceSpaces.PositiveCartesianRealDecoder

/-! # Global normalized physical Cartesian coordinates and real decoding -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraNativeNormalizedHomeomorph (s : ℕ) (hs : 1 ≤ s) :
    MiuraRealSobolevSource s ≃ₜ MiuraRealCartesianTarget :=
  (miuraPhysicalSobolevCartesianHomeomorph s hs).trans
    (miuraSobolevCartesianRealWeightEquiv s).toHomeomorph

theorem miuraNativeNormalizedHomeomorph_apply (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    (miuraNativeNormalizedHomeomorph s hs a).val = miuraSobolevNormalizedCartesianMap s a.val :=
  miuraPhysicalSobolevNormalizedCartesianMap_inclusion s a

def miuraRealCartesianDecoder : (RealCoeff 2 × RealCoeff 2) →L[ℝ] MiuraRealCartesianTarget :=
  (WeightedCoeff.positiveCartesianRealDecoder (Weight.sobolev (1/2)) 2).codRestrict
    miuraCartesianRealSubmodule (fun z => WeightedCoeff.positiveCartesianRealDecoder_real _ _ z)

theorem miuraRealCartesianDecoder_parameters (z : MiuraRealCartesianTarget) :
    miuraRealCartesianDecoder (WeightedCoeff.positiveCartesianRealParameters (Weight.sobolev (1/2)) 2 z.val) = z := by
  apply Subtype.ext
  exact WeightedCoeff.positiveCartesianRealDecoder_parameters _ _ z.val z.property.1 z.property.2

def miuraNativeRealActionFlow (s : ℕ) (a : MiuraRealSobolevSource s) (n : ℕ) (t : ℝ) :
    MiuraRealSobolevSource s :=
  ⟨miuraActionFlow s a.val (fun j => a.property j) n t,miuraActionFlow_real s a.val (fun j => a.property j) n t⟩

theorem miuraNativeNormalizedHomeomorph_actionFlow (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (miuraNativeNormalizedHomeomorph s hs (miuraNativeRealActionFlow s a n t)).val =
      miuraCartesianRotation n t (miuraNativeNormalizedHomeomorph s hs a).val := by
  simp only [miuraNativeNormalizedHomeomorph_apply,miuraNativeRealActionFlow]
  exact miuraSobolevNormalizedCartesianMap_actionFlow s a.val (fun j => a.property j) n hn t

theorem miuraNative_decoded_rotation (s : ℕ) (hs : 1 ≤ s) (z : RealCoeff 2 × RealCoeff 2)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (miuraNativeNormalizedHomeomorph s hs).symm (miuraRealCartesianDecoder (RealCoeff.actionRotation z n t)) =
      miuraNativeRealActionFlow s ((miuraNativeNormalizedHomeomorph s hs).symm (miuraRealCartesianDecoder z)) n (-t) := by
  apply (miuraNativeNormalizedHomeomorph s hs).injective
  apply Subtype.ext
  rw [Homeomorph.apply_symm_apply,miuraNativeNormalizedHomeomorph_actionFlow s hs _ n hn (-t),
    Homeomorph.apply_symm_apply]
  exact WeightedCoeff.positiveCartesianRealDecoder_rotation _ _ z n (by omega) t

end NLS.MKdV
