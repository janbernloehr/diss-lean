import NLS.Dynamics.WeightedRealPhaseFlow
import NLS.SequenceSpaces.RealActionOpening

/-! # One-mode opening in the native weighted real target

The direction is normalized so that its raw selected coefficient is one.
Forgetting the weight gives exactly the original action-opening line.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A native weighted direction with raw first coefficient one at `n`. -/
def weightedActionOpeningDirection (w : Weight) (n : ℤ) :
    WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) :=
  (weightedRealCoordinates w).symm (lp.single p n (w n), 0)

theorem forget_weightedActionOpeningDirection (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (n : ℤ) :
    WeightedRealCoeff.forgetPairWeightCLM w hw (weightedActionOpeningDirection w n) =
      (lp.single p n 1, 0) := by
  have he : weightedRealCoordinates w (weightedActionOpeningDirection (p := p) w n) =
      (lp.single p n (w n), 0) := (weightedRealCoordinates w).apply_symm_apply _
  apply Prod.ext <;> apply lp.ext <;> funext k
  · apply mul_left_cancel₀ (w.positive k).ne'
    rw [← (weightedRealCoordinates_raw w hw _ k).1, he]
    by_cases hk : k = n <;> simp [lp.single_apply, hk]
  · apply mul_left_cancel₀ (w.positive k).ne'
    rw [← (weightedRealCoordinates_raw w hw _ k).2, he]
    simp

/-- Add one real raw amplitude while retaining the native weighted norm. -/
def weightedActionOpening (w : Weight)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p))
    (n : ℤ) (t : ℝ) : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) :=
  z + t • weightedActionOpeningDirection w n

@[simp] theorem weightedActionOpening_zero (w : Weight)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (n : ℤ) :
    weightedActionOpening w z n 0 = z := by simp [weightedActionOpening]

theorem analyticOnNhd_weightedActionOpening (w : Weight)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (n : ℤ) :
    AnalyticOnNhd ℝ (weightedActionOpening w z n) univ := by
  intro t _
  exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)

/-- The raw unweighted line agrees at every amplitude, without rescaling time. -/
theorem forget_weightedActionOpening (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (n : ℤ) (t : ℝ) :
    WeightedRealCoeff.forgetPairWeightCLM w hw (weightedActionOpening w z n t) =
      RealCoeff.actionOpening (WeightedRealCoeff.forgetPairWeightCLM w hw z) n t := by
  simp only [weightedActionOpening, map_add, map_smul,
    forget_weightedActionOpeningDirection, RealCoeff.actionOpening]

end NLS.Birkhoff
