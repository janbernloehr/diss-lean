import NLS.Dynamics.WeightedRealPhaseFlow
import NLS.SequenceSpaces.WeightedRealPairInclusion
import NLS.SequenceSpaces.RealActionReduction

/-! # Compatible normalized complex and real weighted pair coordinates

Both coordinate maps use the actual positive raw weights. Complex inclusion
commutes with normalization and its inverse. Raw quadratic actions acquire
exactly the square of that weight.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Normalize a native weighted complex pair in the ordinary complex pair space. -/
def weightedComplexCoordinates (w : Weight) :
    WeightedCoeffPair w p ≃L[ℂ] (Coeff p × Coeff p) :=
  (WithLp.prodContinuousLinearEquiv p ℂ _ _).trans
    ((WeightedCoeff.weightIsometry w p).toContinuousLinearEquiv.prodCongr
      (WeightedCoeff.weightIsometry w p).toContinuousLinearEquiv)

@[simp] theorem weightedComplexCoordinates_fst (w : Weight) (z : WeightedCoeffPair w p) (n : ℤ) :
    (weightedComplexCoordinates w z).1 n = (w n:ℂ)*z.fst.val n := rfl

@[simp] theorem weightedComplexCoordinates_snd (w : Weight) (z : WeightedCoeffPair w p) (n : ℤ) :
    (weightedComplexCoordinates w z).2 n = (w n:ℂ)*z.snd.val n := rfl

@[simp] theorem weightedComplexCoordinates_symm_fst (w : Weight) (z : Coeff p × Coeff p) (n : ℤ) :
    ((weightedComplexCoordinates w).symm z).fst.val n = z.1 n/(w n:ℂ) := rfl

@[simp] theorem weightedComplexCoordinates_symm_snd (w : Weight) (z : Coeff p × Coeff p) (n : ℤ) :
    ((weightedComplexCoordinates w).symm z).snd.val n = z.2 n/(w n:ℂ) := rfl

/-- Normalization commutes with the actual inclusion of the weighted real form. -/
theorem weightedComplexCoordinates_real (w : Weight)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    weightedComplexCoordinates w (WeightedCoeffPair.complexCLM w z) =
      ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) (weightedRealCoordinates w z) := by
  apply Prod.ext
  · exact (Coeff.complex_coordinateRealEquiv (WeightedCoeff.weightIsometry w p).toContinuousLinearEquiv z.fst).symm
  · exact (Coeff.complex_coordinateRealEquiv (WeightedCoeff.weightIsometry w p).toContinuousLinearEquiv z.snd).symm

/-- Inverse normalization also preserves the full included real pair. -/
theorem weightedComplexCoordinates_symm_real (w : Weight) (z : RealCoeff p × RealCoeff p) :
    (weightedComplexCoordinates w).symm (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z) =
      WeightedCoeffPair.complexCLM w ((weightedRealCoordinates w).symm z) := by
  apply (weightedComplexCoordinates w).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,weightedComplexCoordinates_real,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Normalized quadratic actions are raw physical actions times the squared weight. -/
theorem weightedRealCoordinates_pairAction (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (n : ℤ) :
    RealCoeff.pairAction (weightedRealCoordinates w z) n =
      (w n)^2*RealCoeff.pairAction (WeightedRealCoeff.forgetPairWeightCLM w hw z) n := by
  rw [RealCoeff.pairAction,(weightedRealCoordinates_raw w hw z n).1,
    (weightedRealCoordinates_raw w hw z n).2]
  dsimp only [RealCoeff.pairAction]
  ring

end NLS.Birkhoff
