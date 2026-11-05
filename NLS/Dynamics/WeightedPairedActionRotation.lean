import NLS.SequenceSpaces.RealPairedActionRotationProperties
import NLS.Dynamics.WeightedRealPhaseFlow

/-! # Opposite action rotations in the native weighted pair norm -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

theorem actionRotation_coordinate_mul (a b : RealCoeff p × RealCoeff p)
    (k n : ℤ) (t r : ℝ) (h₁ : a.1 n = r*b.1 n) (h₂ : a.2 n = r*b.2 n) :
    (actionRotation a k t).1 n = r*(actionRotation b k t).1 n ∧
      (actionRotation a k t).2 n = r*(actionRotation b k t).2 n := by
  by_cases hn : n = k
  · subst n
    rw [(actionRotation_apply_same a k t).1,(actionRotation_apply_same a k t).2,
      (actionRotation_apply_same b k t).1,(actionRotation_apply_same b k t).2,h₁,h₂]
    constructor <;> ring
  · rw [(actionRotation_apply_ne a k n hn t).1,(actionRotation_apply_ne a k n hn t).2,
      (actionRotation_apply_ne b k n hn t).1,(actionRotation_apply_ne b k n hn t).2]
    exact ⟨h₁,h₂⟩

theorem pairedActionRotation_coordinate_mul (a b : RealCoeff p × RealCoeff p)
    (k l n : ℤ) (t r : ℝ) (h₁ : a.1 n = r*b.1 n) (h₂ : a.2 n = r*b.2 n) :
    (pairedActionRotation a k l t).1 n = r*(pairedActionRotation b k l t).1 n ∧
      (pairedActionRotation a k l t).2 n = r*(pairedActionRotation b k l t).2 n := by
  have h := actionRotation_coordinate_mul a b k n t r h₁ h₂
  exact actionRotation_coordinate_mul _ _ l n (-t) r h.1 h.2

end RealCoeff
namespace Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def weightedRealPairedActionRotation (w : Weight)
    (a : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (k l : ℤ) (t : ℝ) :
    WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) :=
  (weightedRealCoordinates w).symm (RealCoeff.pairedActionRotation (weightedRealCoordinates w a) k l t)

theorem forget_weightedRealPairedActionRotation (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (a : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (k l : ℤ) (t : ℝ) :
    WeightedRealCoeff.forgetPairWeightCLM w hw (weightedRealPairedActionRotation w a k l t) =
      RealCoeff.pairedActionRotation (WeightedRealCoeff.forgetPairWeightCLM w hw a) k l t := by
  have h (n : ℤ) := RealCoeff.pairedActionRotation_coordinate_mul (weightedRealCoordinates w a)
    (WeightedRealCoeff.forgetPairWeightCLM w hw a) k l n t (w n)
    (weightedRealCoordinates_raw w hw a n).1 (weightedRealCoordinates_raw w hw a n).2
  have he : weightedRealCoordinates w (weightedRealPairedActionRotation w a k l t) =
      RealCoeff.pairedActionRotation (weightedRealCoordinates w a) k l t :=
    (weightedRealCoordinates w).apply_symm_apply _
  apply Prod.ext <;> apply lp.ext <;> funext n
  · have hraw := (weightedRealCoordinates_raw w hw (weightedRealPairedActionRotation w a k l t) n).1
    rw [he] at hraw
    exact mul_left_cancel₀ (w.positive n).ne' (hraw.symm.trans (h n).1)
  · have hraw := (weightedRealCoordinates_raw w hw (weightedRealPairedActionRotation w a k l t) n).2
    rw [he] at hraw
    exact mul_left_cancel₀ (w.positive n).ne' (hraw.symm.trans (h n).2)

set_option maxHeartbeats 800000 in
theorem continuous_weightedRealPairedActionRotation (w : Weight) (k l : ℤ) :
    Continuous (fun x : ℝ × WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) =>
      weightedRealPairedActionRotation w x.2 k l x.1) := by
  have hpair : Continuous (fun x : ℝ × WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) =>
      (x.1,weightedRealCoordinates (p := p) w x.2)) :=
    continuous_fst.prodMk ((weightedRealCoordinates (p := p) w).continuous.comp continuous_snd)
  have hrot := (RealCoeff.continuous_pairedActionRotation (p := p) k l).comp hpair
  exact (weightedRealCoordinates (p := p) w).symm.continuous.comp hrot

end Birkhoff
end NLS
