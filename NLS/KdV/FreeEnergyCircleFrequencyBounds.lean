import NLS.KdV.ClassicalHillWholeGapSquares
import NLS.KdV.FreeFrequencyPsi
import NLS.ComplexAnalysis.RightHalfPlaneSquareRoot
/-! # Principal frequency bounds on the radius-k free energy circles -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillFreeEnergyCircle_frequency_bounds (k : ℕ+) (E : ℂ)
    (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) :
    sqrt E ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/8) ∧
      1/(4*Real.pi) ≤ ‖sqrt E-(Real.pi : ℂ)*(k : ℕ)‖ := by
  let c : ℝ := Real.pi*(k : ℝ)
  have hk : (0 : ℝ) < k := by positivity
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcC : (c : ℂ) = (Real.pi : ℂ)*(k : ℕ) := by simp only [c,ofReal_mul,ofReal_natCast]
  have hcenter : freeHillEnergy k = (c : ℂ)^2 := by
    dsimp only [freeHillEnergy,c]
    push_cast
    ring
  have hR : c*(1/Real.pi) = (k : ℝ) := by dsimp only [c];field_simp
  have hsmall := sqrt_mem_closedBall_of_energy_disc c (1/Real.pi) hc E
    (by rw [← hcenter,hR];exact sphere_subset_closedBall hE)
  have hd : ‖sqrt E-(c : ℂ)‖ ≤ 1/Real.pi := mem_closedBall_iff_norm.mp hsmall
  have hp : 1/Real.pi ≤ Real.pi/8 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  refine ⟨by rw [← hcC];exact closedBall_subset_closedBall hp hsmall,?_⟩
  have hsum : ‖sqrt E+(c : ℂ)‖ ≤ 3*c := by
    have ht := norm_add_le (sqrt E-(c : ℂ)) (2*(c : ℂ))
    rw [show sqrt E-(c : ℂ)+2*(c : ℂ)=sqrt E+(c : ℂ) by ring,
      norm_mul,norm_ofNat,norm_real,Real.norm_eq_abs,abs_of_pos hc] at ht
    dsimp only [c] at ht ⊢
    have hpic : Real.pi ≤ Real.pi*(k : ℝ) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hk1 Real.pi_pos.le
    nlinarith [Real.pi_pos]
  have hprod : ‖sqrt E-(c : ℂ)‖*‖sqrt E+(c : ℂ)‖ = (k : ℝ) := by
    rw [← norm_mul,show (sqrt E-(c : ℂ))*(sqrt E+(c : ℂ))=E-(c : ℂ)^2 by linear_combination sq_sqrt E,
      ← hcenter]
    exact mem_sphere_iff_norm.mp hE
  have hm := mul_le_mul_of_nonneg_left hsum (norm_nonneg (sqrt E-(c : ℂ)))
  rw [hprod] at hm
  have hl : 1 ≤ ‖sqrt E-(c : ℂ)‖*(3*Real.pi) := by
    apply (mul_le_mul_iff_right₀ hk).mp
    dsimp only [c] at hm
    nlinarith
  rw [← hcC]
  apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
  nlinarith [mul_nonneg Real.pi_pos.le (norm_nonneg (sqrt E-(c : ℂ)))]
end NLS.KdV
