import NLS.KdV.FreeHill
import NLS.SequenceSpaces.SobolevPowerMultiplier

/-! # Two derivatives gained by the reduced free Hill resolvent

The resolvent is a bounded map between the actual Sobolev coefficient spaces,
including the infinity endpoint. The estimate keeps the period-two symbol
`pi^2*k^2` and the corrected strip of radius `6*n`.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- The full inhomogeneous second-order weight is controlled by the Hill moment. -/
theorem sobolev_two_le_freeHillValue (k : ℤ) :
    Weight.sobolev 2 k ≤ 2*(1+freeHillValue k) := by
  simp only [Weight.sobolev_apply, Real.rpow_two, freeHillValue]
  have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  nlinarith [sq_abs (k:ℝ), sq_nonneg (|(k:ℝ)|-1),
    mul_nonneg (sub_nonneg.mpr hpi) (sq_nonneg (k:ℝ))]

/-- Quadratic decay of the reduced symbol, with a finite constant for every
point in the strip, including arbitrarily large imaginary parts. -/
theorem sobolev_two_reducedHillSymbol_bound (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    Weight.sobolev 2 k * ‖reducedHillSymbol n hn z hz k‖ ≤ 4 + 2*‖z‖ := by
  by_cases hk : k.natAbs = n
  · simp only [reducedHillSymbol, hk, ↓reduceIte, norm_zero, mul_zero]
    positivity
  · have hd : 1 ≤ ‖z-(freeHillValue k:ℂ)‖ :=
      (show (1:ℝ) ≤ n by exact_mod_cast hn).trans
        (freeHill_denominator_ge_index hn hz hk)
    have hv : 0 ≤ freeHillValue k := by unfold freeHillValue; positivity
    have ht : freeHillValue k ≤ ‖z‖+‖z-(freeHillValue k:ℂ)‖ := by
      calc
        _ = ‖(freeHillValue k:ℂ)‖ := by simp [abs_of_nonneg hv]
        _ = ‖z-(z-(freeHillValue k:ℂ))‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have hw := sobolev_two_le_freeHillValue k
    change Weight.sobolev 2 k * ‖if k.natAbs = n then (0:ℂ) else _‖ ≤ _
    rw [if_neg hk, norm_inv, ← div_eq_mul_inv]
    apply (div_le_iff₀ (by linarith : 0 < ‖z-(freeHillValue k:ℂ)‖)).mpr
    nlinarith [norm_nonneg z, mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hd)]

/-- At every real order and every Banach exponent, the inverse gains two
Sobolev derivatives, with no finite-exponent substitution at the endpoint. -/
theorem exists_sobolevReducedHillResolvent {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s : ℝ) (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    ∃ T : WeightedCoeff (Weight.sobolev s) p →L[ℂ]
        WeightedCoeff (Weight.sobolev (s+2)) p,
      (∀ a k, (T a).val k = reducedHillSymbol n hn z hz k * a.val k) ∧
        ‖T‖ ≤ 4 + 2*‖z‖ := by
  apply WeightedCoeff.exists_sobolev_power_multiplier s 2
    (fun k => reducedHillSymbol n hn z hz k) (4+2*‖z‖) (by positivity)
  intro k
  exact sobolev_two_reducedHillSymbol_bound n hn z hz k

end NLS.KdV
