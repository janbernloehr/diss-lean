import NLS.KdV.FreeHill
import NLS.SequenceSpaces.NegativeSpectralWeight
import NLS.SequenceSpaces.HillMixedKernel

/-! # Weighted-infinity Hill kernel, preliminary pointwise estimates

The strip is the shared corrected radius 6*n. Parameter r=-s lies in
[0,1/2), including the pseudomeasure endpoint r=0.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- The squared Sobolev factor costs at most twice the corresponding bare
power away from a resonant integer mode. -/
theorem sobolev_factor_sq_le (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (j : ℤ) (hj : j≠0) :
    (Weight.sobolev r j)^2 ≤ 2*|(j:ℝ)|^(2*r) := by
  have hj1 : (1:ℝ) ≤ |(j:ℝ)| := by exact_mod_cast (Int.one_le_abs hj)
  have hpos : 0 < |(j:ℝ)| := lt_of_lt_of_le zero_lt_one hj1
  have hb : 1+|(j:ℝ)| ≤ 2*|(j:ℝ)| := by linarith
  calc
    _ = (1+|(j:ℝ)|)^(2*r) := by
      rw [Weight.sobolev_apply, ← Real.rpow_mul_natCast (by positivity)]
      congr 1
      norm_num
      ring
    _ ≤ (2*|(j:ℝ)|)^(2*r) := Real.rpow_le_rpow (by positivity) hb (by positivity)
    _ = (2:ℝ)^(2*r)*|(j:ℝ)|^(2*r) := Real.mul_rpow (by positivity) hpos.le
    _ ≤ 2*|(j:ℝ)|^(2*r) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hpos.le _)
      exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by linarith : 2*r≤1)).trans_eq (Real.rpow_one 2)

/-- The exact denominator factorization preserves the period-two pi^2 symbol. -/
theorem freeHill_inverse_norm_le_product {n : ℕ} (hn : 1≤n) {z : ℂ}
    (hz : z ∈ reducedHillStrip n) {k : ℤ} (hk : k.natAbs≠n) :
    ‖(z-(freeHillValue k:ℂ))⁻¹‖ ≤
      (|(n:ℝ)+(k:ℝ)| * |(n:ℝ)-(k:ℝ)|)⁻¹ := by
  rw [norm_inv]
  have hd := freeHill_denominator_lower hn hz hk
  have he : |(n:ℝ)^2-(k:ℝ)^2| = |(n:ℝ)+(k:ℝ)| *|(n:ℝ)-(k:ℝ)| := by
    rw [← abs_mul]
    congr 1
    ring
  rw [he] at hd
  have hp : 0 < |(n:ℝ)+(k:ℝ)| *|(n:ℝ)-(k:ℝ)| := by
    have hh := nat_le_abs_sq_sub_sq hn hk
    rw [he] at hh
    exact lt_of_lt_of_le (by exact_mod_cast (show 0<n by omega)) hh
  exact inv_anti₀ hp hd

/-- Resonance in signed period-two indices agrees with the natAbs convention
of the shared free Hill resolvent. -/
theorem hill_resonance_iff (n : ℕ) (k : ℤ) :
    k.natAbs = n ↔ k=(n:ℤ) ∨ k=-(n:ℤ) := by
  constructor
  · intro h
    have hh : |k|=(n:ℤ) := by rw [← Int.natCast_natAbs, h]
    rcases le_total 0 k with hk | hk
    · left; simpa only [abs_of_nonneg hk] using hh
    · right; rw [abs_of_nonpos hk] at hh; omega
  · rintro (rfl | rfl) <;> simp

/-- The full Sobolev-weighted reduced symbol has the mixed kernel majorant
at every admissible negative order, with both resonances removed. -/
theorem sobolevReducedSymbol_bound (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    (Weight.sobolev r (k+(n:ℤ)))^2 * ‖reducedHillSymbol n hn z hz k‖ ≤
      2*ReciprocalSeries.mixedHillKernel (1-2*r) n k := by
  by_cases hk : k.natAbs=n
  · have hres := (hill_resonance_iff n k).mp hk
    simp only [reducedHillSymbol, if_pos hk, norm_zero, mul_zero,
      ReciprocalSeries.mixedHillKernel, if_pos hres]
    exact le_rfl
  · have hres : ¬(k=(n:ℤ) ∨ k=-(n:ℤ)) := fun h => hk ((hill_resonance_iff n k).mpr h)
    have hj : k+(n:ℤ) ≠ 0 := by
      intro h
      apply hres
      right
      omega
    have hplus : 0 < |(n:ℝ)+(k:ℝ)| := by
      apply abs_pos.mpr
      exact_mod_cast (show (n:ℤ)+k≠0 by omega)
    have hs := sobolev_factor_sq_le r hr hr1 (k+(n:ℤ)) hj
    simp only [Int.cast_add, Int.cast_natCast, add_comm (k:ℝ) (n:ℝ)] at hs
    have hd := freeHill_inverse_norm_le_product hn hz hk
    have he : |(n:ℝ)+(k:ℝ)|^(2*r) *
        (|(n:ℝ)+(k:ℝ)| * |(n:ℝ)-(k:ℝ)|)⁻¹ =
        ReciprocalSeries.mixedHillKernel (1-2*r) n k := by
      rw [ReciprocalSeries.mixedHillKernel, if_neg hres]
      calc
        _ = (|(n:ℝ)+(k:ℝ)|^(2*r) * |(n:ℝ)+(k:ℝ)|^(-1:ℝ)) *
            |(n:ℝ)-(k:ℝ)|^(-1:ℝ) := by
          simp only [Real.rpow_neg_one, mul_inv, mul_assoc]
        _ = _ := by
          rw [← Real.rpow_add hplus, show 2*r+(-1:ℝ) = -(1-2*r) by ring]
    change (Weight.sobolev r (k+(n:ℤ)))^2 *
      ‖if k.natAbs=n then (0:ℂ) else (z-(freeHillValue k:ℂ))⁻¹‖ ≤ _
    rw [if_neg hk]
    calc
      _ ≤ (2*|(n:ℝ)+(k:ℝ)|^(2*r)) *
          (|(n:ℝ)+(k:ℝ)| * |(n:ℝ)-(k:ℝ)|)⁻¹ :=
        mul_le_mul hs hd (norm_nonneg _) (by positivity)
      _ = _ := by rw [mul_assoc, he]

end NLS.KdV
