import NLS.MKdV.MiuraSobolevCartesianActionFlow
import NLS.ZakharovShabat.SourceHilbertActionSequence

/-! # The complete physical action group on the literal original scalar L² space -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraL2SobolevZeroLift : Coeff 2 →L[ℂ] ScalarSobolev 0 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev ((0 : ℕ) : ℝ)) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem miuraL2SobolevZeroLift_apply (a : Coeff 2) (j : ℤ) :
    (miuraL2SobolevZeroLift a).val j = a j := by
  change a j/(Weight.sobolev ((0 : ℕ) : ℝ) j : ℂ) = a j
  simp only [Nat.cast_zero,Weight.sobolev_zero_apply,Complex.ofReal_one,div_one]

theorem miuraL2SobolevZeroLift_real (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    ∀ j, (miuraL2SobolevZeroLift a).val j = conj ((miuraL2SobolevZeroLift a).val (-j)) := by
  intro j
  simpa only [miuraL2SobolevZeroLift_apply] using ha j

@[simp] theorem miuraL2SobolevZeroLift_L2 (a : Coeff 2) :
    hierarchySobolevJetL2 0 0 le_rfl (miuraL2SobolevZeroLift a) = a := by
  ext j
  simp only [hierarchySobolevJetL2_apply,pow_zero,one_mul,miuraL2SobolevZeroLift_apply]

def miuraOriginalL2ActionFlow (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (t : ℝ) : Coeff 2 :=
  hierarchySobolevJetL2 0 0 le_rfl
    (miuraActionFlow 0 (miuraL2SobolevZeroLift a) (miuraL2SobolevZeroLift_real a ha) n t)

theorem miuraOriginalL2ActionFlow_real (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (t : ℝ) :
    ∀ j, miuraOriginalL2ActionFlow a ha n t j = conj (miuraOriginalL2ActionFlow a ha n t (-j)) := by
  intro j
  simpa only [miuraOriginalL2ActionFlow,hierarchySobolevJetL2_apply,pow_zero,one_mul] using!
    miuraActionFlow_real 0 (miuraL2SobolevZeroLift a) (miuraL2SobolevZeroLift_real a ha) n t j

@[simp] theorem miuraOriginalL2ActionFlow_zero (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) :
    miuraOriginalL2ActionFlow a ha n 0 = a := by
  rw [miuraOriginalL2ActionFlow,miuraActionFlow_zero,miuraL2SobolevZeroLift_L2]

theorem continuous_miuraOriginalL2ActionFlow (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) :
    Continuous (miuraOriginalL2ActionFlow a ha n) :=
  (hierarchySobolevJetL2 0 0 le_rfl).continuous.comp
    (continuous_miuraActionFlow 0 (miuraL2SobolevZeroLift a) (miuraL2SobolevZeroLift_real a ha) n)

theorem miuraOriginalL2ActionFlow_mean (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (t : ℝ) :
    miuraOriginalL2ActionFlow a ha n t 0 = a 0 := by
  change hierarchySobolevJetL2 0 0 le_rfl _ 0 = a 0
  simp only [hierarchySobolevJetL2_apply,pow_zero,one_mul]
  rw [miuraActionFlow_mean_allSobolev,miuraL2SobolevZeroLift_apply]

theorem miuraOriginalL2ActionFlow_Cartesian (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j)))
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (t : ℝ) :
    miuraL2CartesianCoordinates m (miuraOriginalL2ActionFlow a ha n t) =
      if m = n then cartesianPlaneRotation t (miuraL2CartesianCoordinates m a) else miuraL2CartesianCoordinates m a := by
  simpa only [miuraOriginalL2ActionFlow,miuraL2SobolevZeroLift_L2] using!
    miuraL2CartesianCoordinates_miuraActionFlow 0 (miuraL2SobolevZeroLift a)
      (miuraL2SobolevZeroLift_real a ha) m n hm hn t

/-- The entire actual original NLS action sequence, in the full l1 norm,
is fixed on the complete original physical L² orbit. -/
theorem miuraOriginalL2ActionFlow_NLS_actionSequence (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (t : ℝ) :
    sourceHilbertActionSequence miuraActionFlowFamily.psi (scalarL2Diagonal (miuraOriginalL2ActionFlow a ha n t)) =
      sourceHilbertActionSequence miuraActionFlowFamily.psi (scalarL2Diagonal a) := by
  ext k
  rw [miuraActionFlowFamily.data.hilbert_actionSequence_apply _
      (miuraActionFlowFamily.data.real_subset (scalarL2Diagonal_realDiagonal _ (miuraOriginalL2ActionFlow_real a ha n t)).1),
    miuraActionFlowFamily.data.hilbert_actionSequence_apply _
      (miuraActionFlowFamily.data.real_subset (scalarL2Diagonal_realDiagonal a ha).1)]
  simpa only [miuraOriginalL2ActionFlow,miuraL2SobolevZeroLift_L2] using!
    miuraNLSAction_allSobolev_miuraActionFlow 0 (miuraL2SobolevZeroLift a)
      (miuraL2SobolevZeroLift_real a ha) n t k

end NLS.MKdV
