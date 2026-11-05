import NLS.KdV.FreeEnergyCircleFrequencyBounds
import NLS.ComplexAnalysis.ComplexSquareRootShift

/-! # Uniform frequency bounds on complete free energy annuli -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillFreeEnergyAnnulus_frequency_bounds (k : ℕ+) (E : ℂ)
    (hlo : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖) (hhi : ‖E-freeHillEnergy k‖ ≤ 2*(k : ℝ)) :
    sqrt E ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) ∧
      |(sqrt E).im| ≤ 1 ∧ (k : ℝ) ≤ ‖sqrt E‖ ∧
      1/(6*Real.pi) ≤ ‖sqrt E-(Real.pi : ℂ)*(k : ℕ)‖ := by
  let c : ℝ := Real.pi*(k : ℝ)
  have hk : (0 : ℝ) < k := by positivity
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcC : (c : ℂ) = (Real.pi : ℂ)*(k : ℕ) := by simp only [c,ofReal_mul,ofReal_natCast]
  have hcenter : freeHillEnergy k = (c : ℂ)^2 := by
    dsimp only [freeHillEnergy,c]
    push_cast
    ring
  have hd : ‖sqrt E-(c : ℂ)‖ ≤ 2/Real.pi := by
    have h := norm_complexSqrt_sub_positive_le E c (2*(k : ℝ)) hc (by rwa [← hcenter])
    apply h.trans_eq
    dsimp only [c]
    field_simp
  have hp1 : 2/Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  have hpπ : 2/Real.pi ≤ Real.pi/4 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  have hIm : |(sqrt E).im| ≤ 1 := by
    have h := abs_im_le_norm (sqrt E-(c : ℂ))
    simp only [sub_im,ofReal_im,sub_zero] at h
    exact h.trans (hd.trans hp1)
  have hnorm : (k : ℝ) ≤ ‖sqrt E‖ := by
    have h := norm_sub_norm_le (c : ℂ) (sqrt E)
    rw [norm_real,Real.norm_eq_abs,abs_of_pos hc,norm_sub_rev] at h
    have hπ := mul_nonneg hk.le (sub_nonneg.mpr Real.pi_gt_three.le)
    dsimp only [c] at h
    nlinarith [hd.trans hp1]
  have hsum : ‖sqrt E+(c : ℂ)‖ ≤ 3*c := by
    have ht := norm_add_le (sqrt E-(c : ℂ)) (2*(c : ℂ))
    rw [show sqrt E-(c : ℂ)+2*(c : ℂ)=sqrt E+(c : ℂ) by ring,
      norm_mul,norm_ofNat,norm_real,Real.norm_eq_abs,abs_of_pos hc] at ht
    have hc1 : 1 ≤ c := by
      dsimp only [c]
      have h := mul_le_mul_of_nonneg_left hk1 Real.pi_pos.le
      nlinarith [Real.pi_gt_three]
    nlinarith [hd.trans hp1]
  have hprod : (k : ℝ)/2 ≤ ‖sqrt E-(c : ℂ)‖*‖sqrt E+(c : ℂ)‖ := by
    rw [← norm_mul,show (sqrt E-(c : ℂ))*(sqrt E+(c : ℂ))=E-(c : ℂ)^2 by linear_combination sq_sqrt E,
      ← hcenter]
    exact hlo
  have hm := mul_le_mul_of_nonneg_left hsum (norm_nonneg (sqrt E-(c : ℂ)))
  have hl : 1 ≤ ‖sqrt E-(c : ℂ)‖*(6*Real.pi) := by
    apply (mul_le_mul_iff_right₀ hk).mp
    dsimp only [c] at hm
    nlinarith
  refine ⟨?_,hIm,hnorm,?_⟩
  · rw [← hcC,mem_closedBall_iff_norm]
    exact hd.trans hpπ
  · rw [← hcC]
    exact (div_le_iff₀ (by positivity : 0 < 6*Real.pi)).mpr hl

end NLS.KdV
