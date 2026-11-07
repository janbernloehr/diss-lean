import NLS.KdV.HillPhysicalResolventFactorization

/-! Quantitative bounds for the ACTUAL physical periodic resolvent and its
ACTUAL native Riesz contour projection, with all original modes retained. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- A universal positive constant suffices throughout the original rough range. -/
def hillPeriodicProjectionConstant : ℝ := 32*(8*Real.exp 1+2)

/-- Positivity of the explicit original-normalization comparison constant. -/
theorem hillPeriodicProjectionConstant_pos : 0 < hillPeriodicProjectionConstant := by
  unfold hillPeriodicProjectionConstant
  positivity

/-- The ACTUAL physical resolvent difference, multiplied by the original
contour radius, has the logarithmic rough-potential bound in the exact norm. -/
theorem norm_hillContinuousResolvent_sub_zero_mul_index_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (hS : ‖hillHalfSandwich r q z‖ ≤ 1/2) :
    ‖singularHillContinuousResolvent (hillHalfPotentialBase r hr1 q) z-singularHillContinuousResolvent 0 z‖*(n:ℝ) ≤
      hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖ := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  let A := ‖hillHalfDenominatorToContinuous z‖
  let S := ‖hillHalfSandwich r q z‖
  let X := ‖singularHillContinuousResolvent (hillHalfPotentialBase r hr1 q) z-singularHillContinuousResolvent 0 z‖*(n:ℝ)
  let C := 8*Real.exp 1+2
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hA : A^2*(n:ℝ) ≤ C*Real.log (n:ℝ) :=
    (le_div_iff₀ hnpos).mp (norm_sq_hillHalfDenominatorToContinuous_le_log n hn hlog z hz)
  have hS2 : S^2 ≤ 128*C*Real.log (n:ℝ)*(n:ℝ)^(2*r-2)*‖q‖^2 :=
    norm_sq_hillHalfSandwich_le r hr hr1 q n hn hlog z hz
  have hsqrt : (Real.sqrt (n:ℝ))⁻¹*(n:ℝ) = Real.sqrt (n:ℝ) := by
    have hs := Real.sq_sqrt hnpos.le
    have hp := Real.sqrt_pos.mpr hnpos
    rw [inv_mul_eq_div]
    apply (div_eq_iff hp.ne').mpr
    nlinarith
  have hX : X ≤ A*(2*S)*Real.sqrt (n:ℝ) := by
    calc
      X ≤ (A*(2*S)*(Real.sqrt (n:ℝ))⁻¹)*(n:ℝ) :=
        mul_le_mul_of_nonneg_right (norm_singularHillContinuousResolvent_sub_zero_le_half r hr hr1 q n hn hlog z hz hS) hnpos.le
      _ = A*(2*S)*((Real.sqrt (n:ℝ))⁻¹*(n:ℝ)) := by ring
      _ = _ := by rw [hsqrt]
  have hX0 : 0 ≤ X := by dsimp [X];positivity
  have hX2 : X^2 ≤ 512*C^2*(Real.log (n:ℝ))^2*(n:ℝ)^(2*r-2)*‖q‖^2 := by
    calc
      X^2 ≤ (A*(2*S)*Real.sqrt (n:ℝ))^2 := pow_le_pow_left₀ hX0 hX 2
      _ = 4*(A^2*(n:ℝ))*S^2 := by rw [mul_pow,mul_pow,Real.sq_sqrt hnpos.le];ring
      _ ≤ 4*(C*Real.log (n:ℝ))*(128*C*Real.log (n:ℝ)*(n:ℝ)^(2*r-2)*‖q‖^2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hS2 (sq_nonneg S)
          (by positivity [show 0 ≤ Real.log (n:ℝ) by linarith])
      _ = _ := by ring
  have hpow : (n:ℝ)^(2*r-2) = ((n:ℝ)^(r-1))^2 := by
    calc
      _ = (n:ℝ)^((r-1)*(2:ℝ)) := by congr 1;ring
      _ = ((n:ℝ)^(r-1))^(2:ℝ) := Real.rpow_mul hnpos.le _ _
      _ = _ := Real.rpow_two _
  rw [hpow] at hX2
  have htarget0 : 0 ≤ hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖ := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hillPeriodicProjectionConstant_pos.le (by linarith)) (Real.rpow_nonneg hnpos.le _)) (norm_nonneg q)
  change X ≤ _
  have htarget2 : X^2 ≤ (hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖)^2 := by
    unfold hillPeriodicProjectionConstant
    change X^2 ≤ (32*C*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖)^2
    nlinarith [sq_nonneg (C*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖)]
  nlinarith

/-- The genuine native contour integral gives the ACTUAL source periodic
L2-to-continuous projection difference bound, with ONE logarithm. -/
theorem norm_hillContinuousRieszProjection_sub_zero_le_log (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ))
    (hS : ∀ z ∈ sphere (freeHillValue n:ℂ) (n:ℝ), ‖hillHalfSandwich r q z‖ ≤ 1/2) :
    ‖singularHillContinuousRieszProjection (hillHalfPotentialBase r hr1 q) (freeHillValue n:ℂ) (n:ℝ)-
      singularHillContinuousRieszProjection 0 (freeHillValue n:ℂ) (n:ℝ)‖ ≤
      hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖ := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  let D := hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (mul_nonneg hillPeriodicProjectionConstant_pos.le (by linarith)) (Real.rpow_nonneg hnpos.le _)) (norm_nonneg q)
  have hcq : sphere (freeHillValue n:ℂ) (n:ℝ) ⊆ singularHillResolventSet (hillHalfPotentialBase r hr1 q) :=
    fun z hz => mem_singularHillResolventSet_of_halfSandwich_small r hr hr1 q n hn hlog z hz (hS z hz)
  have hc0 : sphere (freeHillValue n:ℂ) (n:ℝ) ⊆ singularHillResolventSet 0 := by
    intro z hz
    have h := mem_singularHillResolventSet_of_halfSandwich_small r hr hr1 0 n hn hlog z hz
      (by rw [hillHalfSandwich_zero r hr hr1 n hn hlog z hz];norm_num)
    simpa only [map_zero] using h
  have hb := norm_singularHillContinuousRieszProjection_sub_le_of_resolvent_bound
    (hillHalfPotentialBase r hr1 q) 0 (freeHillValue n:ℂ) (n:ℝ) hnpos.le hcq hc0 (D/(n:ℝ)) (div_nonneg hD hnpos.le)
    (fun z hz => (le_div_iff₀ hnpos).mpr (norm_hillContinuousResolvent_sub_zero_mul_index_le r hr hr1 q n hn hlog z hz (hS z hz)))
  exact hb.trans_eq (by change (n:ℝ)*(D/(n:ℝ))=D;field_simp [hnpos.ne'])

end NLS.KdV
