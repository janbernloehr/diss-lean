import NLS.KdV.HillPeriodicProjectionBound
import NLS.KdV.HillHalfSandwichSmall

/-! Uniform quantitative convergence of ACTUAL source periodic contour
projections on every original rough-potential Sobolev norm ball. -/
noncomputable section
open Set Metric Filter Topology
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The logarithmic projection majorant tends to zero throughout r<1. -/
theorem tendsto_hillPeriodicProjection_majorant (r R : ℝ) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*R) atTop (𝓝 0) := by
  have ht := (isLittleO_log_rpow_atTop (show 0 < 1-r by linarith)).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  have he (n : ℕ) : Real.log (n:ℝ)/(n:ℝ)^(1-r) = Real.log (n:ℝ)*(n:ℝ)^(r-1) := by
    rw [div_eq_mul_inv,← Real.rpow_neg (Nat.cast_nonneg n),show -(1-r)=r-1 by ring]
  simp only [Function.comp_def,he] at ht
  have h := (ht.const_mul hillPeriodicProjectionConstant).mul_const R
  simpa only [mul_zero,zero_mul,mul_assoc] using h

/-- ONE original Sobolev norm-ball cutoff precedes EVERY complex potential
in the ball and ALL later ORIGINAL indices. The actual continuous-output,
L-infinity and L2 projections obey the SAME one-logarithm bound against the
ACTUAL zero-potential contour projection, with full native circle validity. -/
theorem exists_uniform_hillPeriodicProjection_log_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : WeightedCoeff (Weight.sobolev (-r)) 2, ‖q‖ ≤ R →
      ∀ n : ℕ, N ≤ n → 1 < Real.log (n:ℝ) ∧
        sphere (freeHillValue n:ℂ) (n:ℝ) ⊆ singularHillResolventSet (hillHalfPotentialBase r hr1.le q) ∧
        ‖singularHillContinuousRieszProjection (hillHalfPotentialBase r hr1.le q) (freeHillValue n:ℂ) (n:ℝ)-
          singularHillContinuousRieszProjection 0 (freeHillValue n:ℂ) (n:ℝ)‖ ≤
          hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖ ∧
        ‖singularHillLinfRieszProjection (hillHalfPotentialBase r hr1.le q) (freeHillValue n:ℂ) (n:ℝ)-
          singularHillLinfRieszProjection 0 (freeHillValue n:ℂ) (n:ℝ)‖ ≤
          hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖ ∧
        ‖singularHillL2RieszProjection (hillHalfPotentialBase r hr1.le q) (freeHillValue n:ℂ) (n:ℝ)-
          singularHillL2RieszProjection 0 (freeHillValue n:ℂ) (n:ℝ)‖ ≤
          hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖ := by
  obtain ⟨N,hN,hsmall⟩ := exists_uniform_hillPhysicalHalfSandwich_small r hr hr1 R
  refine ⟨N,hN,?_⟩
  intro q hq n hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hlog,hsmalln⟩ := hsmall n hn
  have hS : ∀ z ∈ sphere (freeHillValue n:ℂ) (n:ℝ), ‖hillHalfSandwich r q z‖ ≤ 1/2 := by
    intro z hz
    have h := hsmalln q hq z hz
    rwa [norm_hillPhysicalHalfSandwich] at h
  have hb := norm_hillContinuousRieszProjection_sub_zero_le_log r hr hr1.le q n hn1 hlog hS
  exact ⟨hlog,fun z hz => mem_singularHillResolventSet_of_halfSandwich_small r hr hr1.le q n hn1 hlog z hz (hS z hz),
    hb,(norm_singularHillLinfRieszProjection_sub_le _ _ _ _).trans hb,
    (norm_singularHillL2RieszProjection_sub_le _ _ _ _).trans hb⟩

/-- Genuine UNIFORM convergence to the actual free projection on EVERY FIXED
original rough-potential norm ball, in all THREE original physical norms.
The ball is chosen before epsilon, not as a tolerance-dependent neighborhood. -/
theorem exists_uniform_hillPeriodicProjection_sub_free_small (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (R : ℝ) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : WeightedCoeff (Weight.sobolev (-r)) 2, ‖q‖ ≤ R →
      ∀ n : ℕ, N ≤ n →
        ‖singularHillContinuousRieszProjection (hillHalfPotentialBase r hr1.le q) (freeHillValue n:ℂ) (n:ℝ)-
          singularHillContinuousRieszProjection 0 (freeHillValue n:ℂ) (n:ℝ)‖ < epsilon ∧
        ‖singularHillLinfRieszProjection (hillHalfPotentialBase r hr1.le q) (freeHillValue n:ℂ) (n:ℝ)-
          singularHillLinfRieszProjection 0 (freeHillValue n:ℂ) (n:ℝ)‖ < epsilon ∧
        ‖singularHillL2RieszProjection (hillHalfPotentialBase r hr1.le q) (freeHillValue n:ℂ) (n:ℝ)-
          singularHillL2RieszProjection 0 (freeHillValue n:ℂ) (n:ℝ)‖ < epsilon := by
  obtain ⟨N0,hN0,hbound⟩ := exists_uniform_hillPeriodicProjection_log_bound r hr hr1 R
  obtain ⟨N1,hN1⟩ := eventually_atTop.mp
    ((tendsto_hillPeriodicProjection_majorant r R hr1).eventually (gt_mem_nhds heps))
  refine ⟨max N0 N1,le_trans hN0 (le_max_left _ _),?_⟩
  intro q hq n hn
  obtain ⟨_,_,hC,hI,hL⟩ := hbound q hq n (le_trans (le_max_left _ _) hn)
  have hn1 : 1 ≤ n := by omega
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hnorm : hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖ ≤
      hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*R :=
    mul_le_mul_of_nonneg_left hq (mul_nonneg (mul_nonneg hillPeriodicProjectionConstant_pos.le hlog)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hlim := hN1 n (le_trans (le_max_right _ _) hn)
  exact ⟨hC.trans hnorm |>.trans_lt hlim,hI.trans hnorm |>.trans_lt hlim,hL.trans hnorm |>.trans_lt hlim⟩

end NLS.KdV
