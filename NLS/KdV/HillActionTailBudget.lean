import NLS.SequenceSpaces.WeightedFourierTail
import NLS.KdV.HillWeightedRealActions

/-! # The Fourier budget for the weighted Hill action tail

The corrected gap remainder provides this explicit budget. It is continuous
in the weighted potential at fixed cutoff and tends to zero for each fixed
potential. Applying it to actual actions also requires a uniform action-gap
comparison on a neighborhood.
-/

noncomputable section
open Filter Topology
namespace NLS.KdV

def hillWeightedActionTailBudget (w : SpectralWeight) (N : ℕ)
    (p : WeightedCoeff w.doubleIndex.toWeight 2) : ℝ :=
  (2 * Real.pi) * (9 * ‖WeightedCoeff.fourierTail (p := 2) w.doubleIndex.toWeight N p‖^2 +
    2304 * ‖p‖^4 / (N : ℝ))

theorem continuous_hillWeightedActionTailBudget (w : SpectralWeight) (N : ℕ) :
    Continuous (hillWeightedActionTailBudget w N) := by
  have ht : Continuous (fun p : WeightedCoeff w.doubleIndex.toWeight 2 =>
      ‖WeightedCoeff.fourierTail (p := 2) w.doubleIndex.toWeight N p‖^2) :=
    (WeightedCoeff.fourierTail (p := 2) w.doubleIndex.toWeight N).continuous.norm.pow 2
  have hn : Continuous (fun p : WeightedCoeff w.doubleIndex.toWeight 2 => ‖p‖^4) :=
    continuous_norm.pow 4
  have h := ((ht.const_mul 9).add ((hn.const_mul 2304).div_const (N : ℝ))).const_mul (2 * Real.pi)
  unfold hillWeightedActionTailBudget
  simpa only [Pi.add_apply] using h

theorem hillWeightedActionTailBudget_eq (w : SpectralWeight) (N : ℕ)
    (p : WeightedCoeff w.doubleIndex.toWeight 2) :
    hillWeightedActionTailBudget w N p =
      (2 * Real.pi) *
        (9 * ‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 p)‖^2 +
          2304 * ‖p‖^4/(N : ℝ)) := by
  unfold hillWeightedActionTailBudget
  rw [WeightedCoeff.norm_eq, WeightedCoeff.weightEquiv_fourierTail]

theorem tendsto_hillWeightedActionTailBudget (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) :
    Tendsto (fun N : ℕ => hillWeightedActionTailBudget w N q) atTop (𝓝 0) := by
  have ht := (WeightedCoeff.tendsto_fourierTail (p := 2) (by norm_num)
    w.doubleIndex.toWeight q).norm.pow 2
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := ((ht.const_mul 9).add (hi.const_mul (2304 * ‖q‖^4))).const_mul (2 * Real.pi)
  simpa only [hillWeightedActionTailBudget, div_eq_mul_inv, norm_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] using h

end NLS.KdV
