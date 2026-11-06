import NLS.ZakharovShabat.SourceSection8SineEstimates
import NLS.KdV.HillL2TraceMeanRemainder
import NLS.KdV.HillL2SmallPotentialTrace
import NLS.KdV.HillL2SourcePrimitive
import NLS.KdV.FreeEnergyAnnulusFrequencyBounds

/-! # Quadratic equal-mean comparison on full complex energy annuli -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

private theorem hillL2Discriminant_annulus_bound (u : Coeff 2)
    (hu : ‖u‖ ≤ 1) (hs : 4*Real.exp 1*‖u‖ ≤ 1) (k : ℕ+) (E : ℂ)
    (hlo : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖) (hhi : ‖E-freeHillEnergy k‖ ≤ 2*(k : ℝ)) :
    ‖hillL2Discriminant (Coeff.periodDouble u) E‖ ≤ 2*Real.exp 1+8*(Real.exp 1)^2 := by
  obtain ⟨_,hIm,hz,_⟩ := hillFreeEnergyAnnulus_frequency_bounds k E hlo hhi
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hn : 1 ≤ ‖sqrt E‖ := hk.trans hz
  have hne : sqrt E ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hn)
  have h := hillL2Discriminant_free_error_small (Coeff.periodDouble u) (sqrt E) hne 1 hIm
    (by rw [Coeff.norm_periodDouble]; exact hs.trans hn)
  rw [sq_sqrt,Coeff.norm_periodDouble] at h
  have hc : ‖cos (sqrt E)‖ ≤ Real.exp 1 :=
    (NLS.ZakharovShabat.section8_norm_cos_le_exp_abs_im _).trans (Real.exp_le_exp.mpr hIm)
  have he : 8*(Real.exp 1)^2*‖u‖/‖sqrt E‖ ≤ 8*(Real.exp 1)^2 := by
    apply (div_le_iff₀ (norm_pos_iff.mpr hne)).mpr
    have h1 := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 8*(Real.exp 1)^2)
    have h2 := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 8*(Real.exp 1)^2)
    nlinarith
  have ht := norm_add_le (hillL2Discriminant (Coeff.periodDouble u) E-2*cos (sqrt E)) (2*cos (sqrt E))
  rw [sub_add_cancel,norm_mul,norm_ofNat] at ht
  linarith

theorem hillL2Radicand_same_mean_annulus_bound (u v : Coeff 2)
    (hmean : u 0 = v 0) (hv : ‖v‖ ≤ ‖u‖) (hu : ‖u‖ ≤ 1) (hs : 4*Real.exp 1*‖u‖ ≤ 1)
    (k : ℕ+) (E : ℂ) (hlo : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖)
    (hhi : ‖E-freeHillEnergy k‖ ≤ 2*(k : ℝ)) :
    ‖hillL2Radicand (Coeff.periodDouble u) E-hillL2Radicand (Coeff.periodDouble v) E‖ ≤
      (32*(Real.exp 1)^3*(4*Real.exp 1+16*(Real.exp 1)^2))*‖u‖^2/(k : ℝ)^2 := by
  obtain ⟨_,hIm,hz,_⟩ := hillFreeEnergyAnnulus_frequency_bounds k E hlo hhi
  have hk : (0 : ℝ) < k := by positivity
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hne : sqrt E ≠ 0 := norm_pos_iff.mp (hk.trans_le hz)
  have hdiff := hillL2Discriminant_same_mean_comparison u v hmean hv (sqrt E) hne 1 hIm
    (hs.trans (hk1.trans hz))
  rw [sq_sqrt] at hdiff
  have hdu := hillL2Discriminant_annulus_bound u hu hs k E hlo hhi
  have hdv := hillL2Discriminant_annulus_bound v (hv.trans hu)
    ((mul_le_mul_of_nonneg_left hv (by positivity)).trans hs) k E hlo hhi
  have hfactor : hillL2Radicand (Coeff.periodDouble u) E-hillL2Radicand (Coeff.periodDouble v) E =
      (hillL2Discriminant (Coeff.periodDouble u) E-hillL2Discriminant (Coeff.periodDouble v) E)*
      (hillL2Discriminant (Coeff.periodDouble u) E+hillL2Discriminant (Coeff.periodDouble v) E) := by
    simp only [hillL2Radicand]
    ring
  rw [hfactor,norm_mul]
  apply (mul_le_mul hdiff ((norm_add_le _ _).trans (add_le_add hdu hdv))
    (norm_nonneg _) (by positivity)).trans
  have hdiv : 32*(Real.exp 1)^3*‖u‖^2/‖sqrt E‖^2 ≤ 32*(Real.exp 1)^3*‖u‖^2/(k : ℝ)^2 := by
    apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hk)
    exact sq_le_sq₀ hk.le (norm_nonneg _) |>.mpr hz
  rw [show (2*Real.exp 1+8*(Real.exp 1)^2)+(2*Real.exp 1+8*(Real.exp 1)^2) =
    4*Real.exp 1+16*(Real.exp 1)^2 by ring]
  calc
    _ ≤ (32*(Real.exp 1)^3*‖u‖^2/(k : ℝ)^2)*(4*Real.exp 1+16*(Real.exp 1)^2) := by
      exact mul_le_mul_of_nonneg_right hdiv (by positivity)
    _ = _ := by ring

theorem hillL2Radicand_annulus_bound (u : Coeff 2)
    (hu : ‖u‖ ≤ 1) (hs : 4*Real.exp 1*‖u‖ ≤ 1) (k : ℕ+) (E : ℂ)
    (hlo : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖) (hhi : ‖E-freeHillEnergy k‖ ≤ 2*(k : ℝ)) :
    ‖hillL2Radicand (Coeff.periodDouble u) E‖ ≤ (2*Real.exp 1+8*(Real.exp 1)^2)^2+4 := by
  have h := hillL2Discriminant_annulus_bound u hu hs k E hlo hhi
  apply (norm_sub_le _ _).trans
  rw [norm_pow,norm_ofNat]
  gcongr

end NLS.KdV
