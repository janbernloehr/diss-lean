import NLS.MKdV.MiuraOriginalL2ActionFlow
import NLS.SequenceSpaces.PositiveCartesianRotations

/-! # Actual native target rotations conjugate the original physical L² action flow -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraCartesianActionVector (n : ℕ) : MiuraPositiveCartesianTarget →L[ℂ] MiuraPositiveCartesianTarget :=
  WeightedCoeff.positiveCartesianActionVector (Weight.sobolev (1/2)) 2 n

def miuraCartesianRotation (n : ℕ) (t : ℝ) : MiuraPositiveCartesianTarget →L[ℂ] MiuraPositiveCartesianTarget :=
  WeightedCoeff.positiveCartesianRotation (Weight.sobolev (1/2)) 2 n t

theorem miuraCartesianRotation_eval (n : ℕ) (m : ℤ) (t : ℝ) (z : MiuraPositiveCartesianTarget) :
    miuraPositiveCartesianEval m (miuraCartesianRotation n t z) =
      if m = n then cartesianPlaneRotation t (miuraPositiveCartesianEval m z) else miuraPositiveCartesianEval m z :=
  WeightedCoeff.positiveCartesianRotation_eval (Weight.sobolev (1/2)) 2 n m t z

theorem miuraCartesianActionVector_eval (n : ℕ) (m : ℤ) (z : MiuraPositiveCartesianTarget) :
    miuraPositiveCartesianEval m (miuraCartesianActionVector n z) =
      if m = n then ((miuraPositiveCartesianEval m z).2,-(miuraPositiveCartesianEval m z).1) else 0 :=
  WeightedCoeff.positiveCartesianActionVector_eval (Weight.sobolev (1/2)) 2 n m z

theorem miuraCartesianRotation_mean (n : ℕ) (t : ℝ) (z : MiuraPositiveCartesianTarget) :
    (miuraCartesianRotation n t z).2 = z.2 :=
  WeightedCoeff.positiveCartesianRotation_mean (Weight.sobolev (1/2)) 2 n t z

@[simp] theorem miuraCartesianRotation_zero (n : ℕ) (z : MiuraPositiveCartesianTarget) :
    miuraCartesianRotation n 0 z = z :=
  WeightedCoeff.positiveCartesianRotation_zero (Weight.sobolev (1/2)) 2 n z

theorem hasDerivAt_miuraCartesianRotation_zero (n : ℕ) (z : MiuraPositiveCartesianTarget) :
    HasDerivAt (fun t => miuraCartesianRotation n t z) (miuraCartesianActionVector n z) 0 :=
  WeightedCoeff.hasDerivAt_positiveCartesianRotation_zero (Weight.sobolev (1/2)) 2 n z

theorem miuraPositiveCartesianMap_positive (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j)))
    (m : ℕ) (hm : 1 ≤ m) :
    miuraPositiveCartesianEval m (miuraPositiveCartesianMap a) = miuraL2CartesianCoordinates m a := by
  change ((WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence a).1).val.val m,
    (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence a).2).val.val m) = _
  rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply,
    if_pos (by omega : (0 : ℤ) < m),if_pos (by omega : (0 : ℤ) < m)]
  exact miuraL2CartesianSequence_positive a ha m hm

/-- Equality in the full native Banach target, retaining all positive
coordinates and the signed mean for the entire original physical orbit. -/
theorem miuraPositiveCartesianMap_originalActionFlow (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j)))
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    miuraPositiveCartesianMap (miuraOriginalL2ActionFlow a ha n t) =
      miuraCartesianRotation n t (miuraPositiveCartesianMap a) := by
  apply WeightedCoeff.positivePairMean_ext
  · intro m hm
    have hi : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm.le
    have hnat : 1 ≤ m.toNat := by omega
    have hA := miuraPositiveCartesianMap_positive a ha m.toNat hnat
    have hB := miuraPositiveCartesianMap_positive (miuraOriginalL2ActionFlow a ha n t)
      (miuraOriginalL2ActionFlow_real a ha n t) m.toNat hnat
    rw [hi] at hA hB
    change miuraPositiveCartesianEval m (miuraPositiveCartesianMap (miuraOriginalL2ActionFlow a ha n t)) =
      miuraPositiveCartesianEval m (miuraCartesianRotation n t (miuraPositiveCartesianMap a))
    rw [miuraCartesianRotation_eval,hA,hB]
    have hmn : m = (n : ℤ) ↔ m.toNat = n := by omega
    simpa only [hmn] using miuraOriginalL2ActionFlow_Cartesian a ha m.toNat n hnat hn t
  · rw [miuraCartesianRotation_mean]
    exact miuraOriginalL2ActionFlow_mean a ha n t

end NLS.MKdV
