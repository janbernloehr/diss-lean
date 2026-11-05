import NLS.KdV.FreeContourUniformLowerBound
import NLS.KdV.HillL2DirichletError
import NLS.KdV.HillAllDirichletTerminals
import NLS.ComplexAnalysis.SineNormEstimates

/-! # Inverse-index displacement of the actual complex Dirichlet frequency

A Dirichlet zero in the already proved small energy disc has an O(||q||/k)
frequency displacement. This uses the actual characteristic equation,
not real spectral localization or pointwise continuity.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillDirichlet_frequency_displacement_bound (k : ℕ+) (p : Coeff 2) (E : ℂ)
    (hp : ‖p‖ ≤ 1/(16*Real.exp 1))
    (hE : ‖E-freeHillEnergy k‖ ≤ (k : ℝ)/16)
    (hzero : hillL2DirichletCharacteristic p E = 0) :
    (k : ℝ) ≤ ‖sqrt E‖ ∧ |(sqrt E).im| ≤ 1 ∧
      ‖sqrt E-(Real.pi : ℂ)*(k : ℕ)‖ ≤ 1/2 ∧
      ‖sqrt E-(Real.pi : ℂ)*(k : ℕ)‖ ≤ 8*(Real.exp 1)^2*‖p‖/(k : ℝ) := by
  let z := sqrt E
  let c : ℝ := (k : ℝ)*Real.pi
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hkp : (0 : ℝ) < k := by positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hfree : freeHillEnergy k = (c : ℂ)^2 := by
    simp only [freeHillEnergy,c,ofReal_pow,ofReal_mul,ofReal_natCast]
  have hδ := norm_complexSqrt_sub_positive_le E c ((k : ℝ)/16) hc (by rwa [← hfree])
  have hδhalf : ‖z-(c : ℂ)‖ ≤ 1/2 := by
    apply hδ.trans
    apply (div_le_iff₀ hc).mpr
    dsimp only [c]
    nlinarith [Real.pi_gt_three]
  have hzlo : (k : ℝ) ≤ ‖z‖ := by
    have h := norm_sub_norm_le (c : ℂ) z
    rw [norm_real,Real.norm_eq_abs,abs_of_pos hc,norm_sub_rev] at h
    dsimp only [c] at hδhalf h
    nlinarith [Real.pi_gt_three]
  have hzn : 0 < ‖z‖ := hkp.trans_le hzlo
  have hz : z ≠ 0 := norm_pos_iff.mp hzn
  have him : |z.im| ≤ 1 := by
    have h := abs_im_le_norm (z-(c : ℂ))
    simp only [sub_im,ofReal_im,sub_zero] at h
    linarith
  have hsmall : 4*Real.exp 1*‖p‖ ≤ ‖z‖ := by
    have hb := (le_div_iff₀ (by positivity : 0 < 16*Real.exp 1)).mp hp
    nlinarith
  have hsin : ‖sin z‖ ≤ 4*(Real.exp 1)^2*‖p‖/‖z‖ := by
    have h := hillL2DirichletCharacteristic_free_error_small p z hz 1 him hsmall
    have he : z^2 = E := sq_sqrt E
    rw [he,hzero,zero_sub,norm_neg,norm_div] at h
    calc
      _ ≤ (4*(Real.exp 1)^2*‖p‖/‖z‖^2)*‖z‖ := (div_le_iff₀ hzn).mp h
      _ = _ := by field_simp
  have hδsin : ‖z-(Real.pi : ℂ)*(k : ℕ)‖ ≤ 2*‖sin z‖ := by
    have hcC : (c : ℂ) = (Real.pi : ℂ)*(k : ℕ) := by simp only [c,ofReal_mul,ofReal_natCast]; ring
    rw [hcC] at hδhalf
    have h := norm_le_two_mul_complex_sin (z-(Real.pi : ℂ)*(k : ℕ)) hδhalf
    rwa [norm_sin_sub_free_center] at h
  have hδsmall : ‖z-(Real.pi : ℂ)*(k : ℕ)‖ ≤ 1/2 := by
    simpa only [c,ofReal_mul,ofReal_natCast,mul_comm] using hδhalf
  refine ⟨hzlo,him,hδsmall,hδsin.trans ?_⟩
  apply (mul_le_mul_of_nonneg_left hsin (by norm_num : (0 : ℝ) ≤ 2)).trans
  have hd := div_le_div_of_nonneg_left (by positivity : 0 ≤ 4*(Real.exp 1)^2*‖p‖) hkp hzlo
  exact (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

end NLS.KdV
