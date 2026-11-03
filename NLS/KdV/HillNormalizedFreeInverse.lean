import NLS.KdV.HillNormalizedResolvent

/-! Identification of the actual zero-potential normalized inverse with
the original free phase inverse on the entire coefficient Hilbert space. -/
noncomputable section
open Set Metric
namespace NLS.KdV

/-- The genuine full normalized perturbation is zero for the zero potential. -/
theorem hillHalfSandwich_zero (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (hlog : 1 < Real.log (n:ℝ)) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) : hillHalfSandwich r 0 z = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  ext k
  rw [hillHalfSandwich_apply r hr hr1 0 n hn hlog z hz]
  simp

/-- The actual normalized zero-potential inverse is exactly the free phase inverse. -/
theorem hillNormalizedInverse_zero (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (hlog : 1 < Real.log (n:ℝ)) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    hillNormalizedInverse r 0 z = hillNormalizedPhaseInverse z := by
  have h := hillNormalizedInverse_sub_phaseInverse r 0 n hn z hz
    (by rw [hillHalfSandwich_zero r hr hr1 n hn hlog z hz];norm_num)
  rw [hillHalfSandwich_zero r hr hr1 n hn hlog z hz,
    ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero] at h
  exact sub_eq_zero.mp h

end NLS.KdV
