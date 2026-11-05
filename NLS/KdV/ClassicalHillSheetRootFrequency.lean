import NLS.KdV.ClassicalHillSheetRootBorn
import NLS.ComplexAnalysis.SineNormEstimates

/-! # Frequency comparison for the actual Hill sheet-root leading term -/
noncomputable section
open Set Metric Complex MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

theorem classicalHillSheetRoot_frequency_remainder_bound (q : Curve ℂ)
    (z : ℂ) (hz : z ≠ 0) (r H : ℝ) (hH : |z.im| ≤ H)
    (hsmall : Real.exp H/‖z‖*classicalHillPotentialMass q ≤ 1/2) :
    ‖z*(2*(classicalHillFlow q (z^2) (0,1) 1).2-classicalHillDiscriminant q (z^2))-
      ∫ s in (0 : ℝ)..1, sin ((r : ℂ)*((2*s-1 : ℝ) : ℂ))*NLS.LinearVolterra.extend q s‖ ≤
      4*(Real.exp H)^3*(classicalHillPotentialMass q)^2/‖z‖+
        Real.exp ‖z-r‖*‖z-r‖*classicalHillPotentialMass q := by
  let L : ℂ → ℂ := fun w => ∫ s in (0 : ℝ)..1,
    sin (w*((2*s-1 : ℝ) : ℂ))*NLS.LinearVolterra.extend q s
  have hL : z*classicalHillSheetRootBorn q z = L z := by
    rw [classicalHillSheetRootBorn,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [L]
    field_simp
  have hdiff : L z-L r = ∫ s in (0 : ℝ)..1,
      (sin (z*((2*s-1 : ℝ) : ℂ))-sin ((r : ℂ)*((2*s-1 : ℝ) : ℂ)))*NLS.LinearVolterra.extend q s := by
    have hc (w : ℂ) : Continuous (fun s : ℝ => sin (w*((2*s-1 : ℝ) : ℂ))*NLS.LinearVolterra.extend q s) := by
      have hs : Continuous (fun s : ℝ => sin (w*((2*s-1 : ℝ) : ℂ))) := by fun_prop
      exact hs.mul (continuous_extend q)
    rw [← intervalIntegral.integral_sub (f := fun s => sin (z*((2*s-1 : ℝ) : ℂ))*NLS.LinearVolterra.extend q s)
      (g := fun s => sin ((r : ℂ)*((2*s-1 : ℝ) : ℂ))*NLS.LinearVolterra.extend q s)
      ((hc z).intervalIntegrable 0 1) ((hc r).intervalIntegrable 0 1)]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  have hdiff_bound : ‖L z-L r‖ ≤ Real.exp ‖z-r‖*‖z-r‖*classicalHillPotentialMass q := by
    rw [hdiff]
    have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        ‖(sin (z*((2*s-1 : ℝ) : ℂ))-sin ((r : ℂ)*((2*s-1 : ℝ) : ℂ)))*NLS.LinearVolterra.extend q s‖ ≤
          (Real.exp ‖z-r‖*‖z-r‖)*‖NLS.LinearVolterra.extend q s‖ := by
      have ht : |2*s-1| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
      have hd : ‖z*((2*s-1 : ℝ) : ℂ)-(r : ℂ)*((2*s-1 : ℝ) : ℂ)‖ ≤ ‖z-r‖ := by
        rw [← sub_mul,norm_mul,norm_real,Real.norm_eq_abs]
        exact mul_le_of_le_one_right (norm_nonneg _) ht
      have h := norm_complex_sin_sub_le_exp (z*((2*s-1 : ℝ) : ℂ)) ((r : ℂ)*((2*s-1 : ℝ) : ℂ))
      simp only [mul_im,ofReal_im,mul_zero,zero_add,zero_mul,abs_zero,zero_add] at h
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (h.trans (mul_le_mul (Real.exp_le_exp.mpr hd) hd
        (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _)
    have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (Filter.Eventually.of_forall (fun s hs => hb s ⟨hs.1.le,hs.2⟩))
      ((continuous_const.mul (continuous_extend q).norm).intervalIntegrable 0 1)
    simpa only [intervalIntegral.integral_const_mul,classicalHillPotentialMass] using hi
  have hborn := classicalHillSheetRoot_born_remainder_bound q z hz H hH hsmall
  have hmain : ‖z*(2*(classicalHillFlow q (z^2) (0,1) 1).2-classicalHillDiscriminant q (z^2))-L z‖ ≤
      4*(Real.exp H)^3*(classicalHillPotentialMass q)^2/‖z‖ := by
    rw [← hL,← mul_sub,norm_mul]
    apply (mul_le_mul_of_nonneg_left hborn (norm_nonneg z)).trans_eq
    field_simp
  exact (norm_sub_le_norm_sub_add_norm_sub _ (L z) (L r)).trans (add_le_add hmain hdiff_bound)

end NLS.KdV
