import NLS.KdV.FreeEnergyCircleFrequencyBounds
import NLS.ComplexAnalysis.AffineLoopHomotopy
/-! # A common energy shell for the inner squared-circle deformation

The complete affine homotopy stays between radius k and pi^2*k/4.
Its principal frequencies stay on the already covered positive annuli.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped unitInterval
namespace NLS.KdV

theorem hillFreeEnergyShell_frequency_bounds (k : ℕ+) (E : ℂ)
    (hE : E ∈ closedBall (freeHillEnergy k) (Real.pi^2/4*(k : ℝ)))
    (hfar : (k : ℝ) ≤ ‖E-freeHillEnergy k‖) :
    sqrt E ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) ∧
      1/(4*Real.pi) ≤ ‖sqrt E-(Real.pi : ℂ)*(k : ℕ)‖ := by
  let c : ℝ := Real.pi*(k : ℝ)
  have hk : (0 : ℝ) < k := by positivity
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hc : 0 < c := by dsimp only [c];positivity
  have hcC : (c : ℂ) = (Real.pi : ℂ)*(k : ℕ) := by simp only [c,ofReal_mul,ofReal_natCast]
  have hcenter : freeHillEnergy k = (c : ℂ)^2 := by dsimp only [freeHillEnergy,c];push_cast;ring
  have hR : c*(Real.pi/4) = Real.pi^2/4*(k : ℝ) := by dsimp only [c];ring
  have hsmall := sqrt_mem_closedBall_of_energy_disc c (Real.pi/4) hc E (by rwa [← hcenter,hR])
  have hd := mem_closedBall_iff_norm.mp hsmall
  refine ⟨by simpa only [hcC] using hsmall,?_⟩
  have hsum : ‖sqrt E+(c : ℂ)‖ ≤ 3*c := by
    have ht := norm_add_le (sqrt E-(c : ℂ)) (2*(c : ℂ))
    rw [show sqrt E-(c : ℂ)+2*(c : ℂ)=sqrt E+(c : ℂ) by ring,
      norm_mul,norm_ofNat,norm_real,Real.norm_eq_abs,abs_of_pos hc] at ht
    have hpic : Real.pi ≤ c := by dsimp only [c];simpa only [mul_one] using mul_le_mul_of_nonneg_left hk1 Real.pi_pos.le
    linarith
  have hprod : (k : ℝ) ≤ ‖sqrt E-(c : ℂ)‖*‖sqrt E+(c : ℂ)‖ := by
    rw [← norm_mul,show (sqrt E-(c : ℂ))*(sqrt E+(c : ℂ))=E-(c : ℂ)^2 by linear_combination sq_sqrt E,
      ← hcenter]
    exact hfar
  have hm := mul_le_mul_of_nonneg_left hsum (norm_nonneg (sqrt E-(c : ℂ)))
  have hl : 1 ≤ ‖sqrt E-(c : ℂ)‖*(3*Real.pi) := by
    apply (mul_le_mul_iff_right₀ hk).mp
    dsimp only [c] at hm
    nlinarith
  rw [← hcC]
  apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
  nlinarith [mul_nonneg Real.pi_pos.le (norm_nonneg (sqrt E-(c : ℂ)))]

theorem hillFreeEnergyCircle_squaredCircle_homotopy_shell (k : ℕ+) (s : I) (theta : ℝ) :
    let v := AffineMap.lineMap (circleMap (freeHillEnergy k) (k : ℝ) theta)
      ((circleMap ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/16) theta)^2) (s : ℝ)
    v ∈ closedBall (freeHillEnergy k) (Real.pi^2/4*(k : ℝ)) ∧ (k : ℝ) ≤ ‖v-freeHillEnergy k‖ := by
  let c : ℝ := Real.pi*(k : ℝ)
  let r := Real.pi/16
  let A := (1-(s : ℝ))*(k : ℝ)+(s : ℝ)*2*c*r
  let B := (s : ℝ)*r^2
  let e := Complex.exp ((theta : ℂ)*Complex.I)
  let v := AffineMap.lineMap (circleMap (freeHillEnergy k) (k : ℝ) theta)
      ((circleMap ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/16) theta)^2) (s : ℝ)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hc : 0 < c := by dsimp only [c];positivity
  have hr : 0 < r := by dsimp only [r];positivity
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : 0 ≤ 1-(s : ℝ) := sub_nonneg.mpr s.property.2
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have heunit : ‖e‖ = 1 := norm_exp_ofReal_mul_I theta
  have heq : v-freeHillEnergy k = e*((A : ℂ)+(B : ℂ)*e) := by
    dsimp only [v,A,B,c,r,e,freeHillEnergy]
    simp only [circleMap,AffineMap.lineMap_apply_module,Complex.real_smul]
    push_cast
    ring
  have hu : ‖v-freeHillEnergy k‖ ≤ A+B := by
    rw [heq,norm_mul,heunit,one_mul]
    simpa only [norm_real,Real.norm_eq_abs,abs_of_nonneg hA,norm_mul,abs_of_nonneg hB,heunit,mul_one] using norm_add_le (A : ℂ) ((B : ℂ)*e)
  have hl : A-B ≤ ‖v-freeHillEnergy k‖ := by
    rw [heq,norm_mul,heunit,one_mul]
    have hh := norm_sub_norm_le (A : ℂ) (-((B : ℂ)*e))
    rw [norm_real,Real.norm_eq_abs,abs_of_nonneg hA,norm_neg,norm_mul,
      norm_real,Real.norm_eq_abs,abs_of_nonneg hB,heunit,mul_one,sub_neg_eq_add] at hh
    exact hh
  have hpic : Real.pi ≤ c := by dsimp only [c];simpa only [mul_one] using mul_le_mul_of_nonneg_left hk1 Real.pi_pos.le
  have hleft : (k : ℝ) ≤ 2*c*r-r^2 := by
    have hpi : 0 ≤ Real.pi^2-9 := by nlinarith [Real.pi_gt_three]
    have hp := mul_nonneg hpi (sub_nonneg.mpr hk1)
    dsimp only [c,r]
    nlinarith [Real.pi_gt_three]
  have hright : 2*c*r+r^2 ≤ c*Real.pi/4 := by
    have hh := mul_le_mul_of_nonneg_right (show r ≤ c/16 by dsimp only [r];linarith) hr.le
    dsimp only [r] at hh ⊢
    nlinarith [mul_pos hc Real.pi_pos]
  have hstart : (k : ℝ) ≤ c*Real.pi/4 := by
    dsimp only [c]
    have hh := mul_nonneg (show 0 ≤ Real.pi^2-4 by nlinarith [Real.pi_gt_three]) (show (0 : ℝ) ≤ k by positivity)
    nlinarith
  have hABlo : (k : ℝ) ≤ A-B := by
    dsimp only [A,B]
    nlinarith [mul_nonneg s.property.1 (sub_nonneg.mpr hleft)]
  have hABhi : A+B ≤ c*Real.pi/4 := by
    dsimp only [A,B]
    nlinarith [mul_nonneg (show 0 ≤ 1-(s : ℝ) by linarith [s.property.2]) (sub_nonneg.mpr hstart),
      mul_nonneg s.property.1 (sub_nonneg.mpr hright)]
  refine ⟨mem_closedBall_iff_norm.mpr (hu.trans ?_),hABlo.trans hl⟩
  dsimp only [c] at hABhi
  nlinarith
end NLS.KdV
