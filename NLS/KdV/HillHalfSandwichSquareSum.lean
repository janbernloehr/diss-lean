import NLS.KdV.HillHalfSandwichMatrix
import NLS.SequenceSpaces.SquareSummableMatrix

/-! Genuine summability and quantitative FULL squared-entry bounds for the
actual source S_lambda matrix with rough original H^(-r) potentials. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV

/-- Every potential-frequency row of the actual squared matrix is summable. -/
theorem summable_hillHalfSandwichMatrix_shift (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    Summable (fun m : ℤ => ‖hillHalfSandwichMatrix r q z (m+k) m‖^2) := by
  have hs := (summable_hillSandwich_row r hr hr1 n hn z hz k).mul_left
    (‖WeightedCoeff.weightEquiv (Weight.sobolev (-r)) 2 q k‖^2)
  simpa only [norm_sq_hillHalfSandwichMatrix_shift] using hs

/-- The actual row sum has a majorant whose k dependence is exactly the
summable squared original H^(-r) potential coefficient. -/
theorem tsum_hillHalfSandwichMatrix_shift_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    (∑' m : ℤ, ‖hillHalfSandwichMatrix r q z (m+k) m‖^2) ≤
      ‖WeightedCoeff.weightEquiv (Weight.sobolev (-r)) 2 q k‖^2 *
        (128*(8*Real.exp 1+2)*Real.log (n:ℝ)*(n:ℝ)^(2*r-2)) := by
  simp only [norm_sq_hillHalfSandwichMatrix_shift,tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_hillSandwich_row_le_log r hr hr1 n hn hlog z hz k) (sq_nonneg _)

/-- The FULL actual complex matrix has summable squared entries; this is
proved for all original modes, rather than postulated in an operator construction. -/
theorem summable_hillHalfSandwichMatrix_sq (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    Summable (fun p : ℤ × ℤ => ‖hillHalfSandwichMatrix r q z p.1 p.2‖^2) := by
  have hq := (lp.hasSum_norm (p := 2) (by norm_num)
    (WeightedCoeff.weightEquiv (Weight.sobolev (-r)) 2 q)).summable
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hq
  have hrows : Summable (fun k : ℤ => ∑' m : ℤ, ‖hillHalfSandwichMatrix r q z (m+k) m‖^2) :=
    (hq.mul_right _).of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => sq_nonneg _))
      (tsum_hillHalfSandwichMatrix_shift_le r hr hr1 q n hn hlog z hz)
  have hprod : Summable (fun p : ℤ × ℤ => ‖hillHalfSandwichMatrix r q z (p.2+p.1) p.2‖^2) :=
    (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
      ⟨summable_hillHalfSandwichMatrix_shift r hr hr1 q n hn z hz,hrows⟩
  exact hillMatrixFrequencyShear.summable_iff.mp hprod

/-- The FULL squared-entry sum has the sharp decay for every source
-1<t<-1/2, with the original H^t norm and no coordinate loss. -/
theorem tsum_hillHalfSandwichMatrix_sq_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    (∑' p : ℤ × ℤ, ‖hillHalfSandwichMatrix r q z p.1 p.2‖^2) ≤
      (128*(8*Real.exp 1+2)*Real.log (n:ℝ)*(n:ℝ)^(2*r-2))*‖q‖^2 := by
  have hs := summable_hillHalfSandwichMatrix_sq r hr hr1 q n hn hlog z hz
  have hq := (lp.hasSum_norm (p := 2) (by norm_num)
    (WeightedCoeff.weightEquiv (Weight.sobolev (-r)) 2 q))
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hq
  have hrows : Summable (fun k : ℤ => ∑' m : ℤ, ‖hillHalfSandwichMatrix r q z (m+k) m‖^2) :=
    (hillMatrixFrequencyShear.summable_iff.mpr hs).prod
  have he : (∑' p : ℤ × ℤ, ‖hillHalfSandwichMatrix r q z p.1 p.2‖^2) =
      ∑' k : ℤ, ∑' m : ℤ, ‖hillHalfSandwichMatrix r q z (m+k) m‖^2 := by
    rw [← hillMatrixFrequencyShear.tsum_eq (fun p : ℤ × ℤ => ‖hillHalfSandwichMatrix r q z p.1 p.2‖^2)]
    exact (hillMatrixFrequencyShear.summable_iff.mpr hs).tsum_prod
  rw [he]
  have hb := hrows.tsum_le_tsum
    (tsum_hillHalfSandwichMatrix_shift_le r hr hr1 q n hn hlog z hz) (hq.summable.mul_right _)
  rw [tsum_mul_right,hq.tsum_eq] at hb
  simpa only [← WeightedCoeff.norm_eq,mul_comm] using hb

end NLS.KdV
