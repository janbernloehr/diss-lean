import NLS.KdV.HillFreeMultiplierCutoffs

/-! One global exponential multiplier bound works before ALL positive
row and numerator indices. Its error bound vanishes at zero, providing
the actual nonlinear l2 period map's differentiability estimate. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem norm_hillFreePeriodMultiplierApprox_sub_le (n m : ℕ+) (hmn : m ≠ n)
    (N : ℕ) (hN : (m:ℕ) ≤ N) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    ‖hillFreePeriodMultiplierApprox n m N d-hillFreePeriodMultiplierApprox n m N 0‖ ≤
      ‖hillFreePeriodMultiplierApprox n m N 0‖*(Real.exp (hillFreeInteractionConstant*‖d‖)-1) := by
  rw [hillFreePeriodMultiplierApprox_factor n m hmn N hN,
    ← mul_sub_one,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (Finset.norm_prod_one_add_sub_one_le _ _).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr (sum_norm_hillFreeInteractionPerturbation_le n m d _)) 1)

theorem norm_hillFreePeriodMultiplier_sub_one_le (n m : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    ‖hillFreePeriodMultiplier n m d-1‖ ≤ Real.exp (hillFreeInteractionConstant*‖d‖)-1 := by
  by_cases hmn : m = n
  · simp only [hillFreePeriodMultiplier,if_pos hmn,sub_self,norm_zero]
    exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hillFreeInteractionConstant_nonneg (norm_nonneg _)))
  have hL : Tendsto (fun N => ‖hillFreePeriodMultiplierApprox n m N d-
      hillFreePeriodMultiplierApprox n m N 0‖) atTop (𝓝 ‖hillFreePeriodMultiplier n m d-1‖) := by
    simpa only [hillFreePeriodMultiplier_zero] using
      ((tendsto_hillFreePeriodMultiplierApprox n m d).sub (tendsto_hillFreePeriodMultiplierApprox n m 0)).norm
  have hR : Tendsto (fun N => ‖hillFreePeriodMultiplierApprox n m N 0‖*
      (Real.exp (hillFreeInteractionConstant*‖d‖)-1)) atTop
      (𝓝 (Real.exp (hillFreeInteractionConstant*‖d‖)-1)) := by
    simpa only [hillFreePeriodMultiplier_zero,norm_one,one_mul] using
      (tendsto_hillFreePeriodMultiplierApprox n m 0).norm.mul_const
        (Real.exp (hillFreeInteractionConstant*‖d‖)-1)
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [eventually_ge_atTop (m:ℕ)] with N hN
  exact norm_hillFreePeriodMultiplierApprox_sub_le n m hmn N hN d

theorem norm_hillFreePeriodMultiplier_le (n m : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    ‖hillFreePeriodMultiplier n m d‖ ≤ Real.exp (hillFreeInteractionConstant*‖d‖) := by
  have h := norm_le_norm_sub_add (hillFreePeriodMultiplier n m d) 1
  rw [norm_one] at h
  linarith [norm_hillFreePeriodMultiplier_sub_one_le n m d]

theorem norm_hillFreePeriodEquationRow_le (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ))
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    ‖hillFreePeriodEquationRow n m D d‖ ≤ Real.exp (hillFreeInteractionConstant*‖d‖)*‖d m‖ := by
  rw [hillFreePeriodEquationRow_factor,norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_hillFreePeriodMultiplier_le n m d) (norm_nonneg _)

theorem norm_hillFreePeriodEquationRow_sub_coordinate_le (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ))
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    ‖hillFreePeriodEquationRow n m D d-d m‖ ≤
      (Real.exp (hillFreeInteractionConstant*‖d‖)-1)*‖d m‖ := by
  rw [hillFreePeriodEquationRow_factor,← mul_sub_one,norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_hillFreePeriodMultiplier_sub_one_le n m d) (norm_nonneg _)

end NLS.KdV
