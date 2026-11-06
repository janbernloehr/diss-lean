import NLS.KdV.HillHminusOneHighGapPairs
import NLS.ZakharovShabat.UniformCanonicalPeriodicEndpoints

/-! # Actual rough Hill gaps controlled by diagonal NLS gaps

The translated principal square roots of both actual Hill endpoints lie
in one distant NLS strip. Its complete spectral pair then controls their
difference, without ordering the complex endpoints or excluding double roots.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem HillHminusMiuraChart.sqrt_root_mem_periodicSpectrum
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (lambda : ℂ) (hz : hillHminusRadicand q lambda = 0) :
    sqrt (lambda+C.energyShift) ∈ periodicSpectrum (by simp)
      (periodOnePotential (hillMiuraDiagonal (C.lift q))) := by
  apply (canonicalPeriodicProduct_eq_zero_iff (by simp) (by norm_num) _ _).mp
  rw [canonicalPeriodic_eq_discriminant_sq_sub_four_finite (by simp) (by norm_num)
    _ (periodOnePotential_mem _) _]
  have ht : hillHminusDiscriminant q lambda = canonicalDiscriminant (by simp)
      (periodOnePotential (hillMiuraDiagonal (C.lift q))) (sqrt (lambda+C.energyShift)) := by
    rw [hillHminusDiscriminant_eq_chart C q hq]
    rfl
  rw [← ht]
  exact hz

theorem HillHminusHighGapPair.gap_le_diagonal_gap
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (n : ℕ+) (r : ℝ) (l u x y : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (hr : r ≤ Real.pi/4)
    (hshift : ‖C.energyShift‖ ≤ Real.pi*(n : ℕ)*(Real.pi/4))
    (hNLS : PeriodicEndpointPair (by simp)
      (periodOnePotential (hillMiuraDiagonal (C.lift q))) (n : ℤ) x y) :
    ‖l-u‖ ≤ (3*Real.pi)*(n : ℕ)*‖x-y‖ := by
  let c : ℝ := Real.pi*(n : ℕ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcpi : Real.pi ≤ c := by
    have hn : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
    dsimp [c]
    nlinarith [Real.pi_pos]
  have hcenter : ((Real.pi : ℂ)*(n : ℕ))^2 = (c : ℂ)^2 := by simp [c]
  have hroot (z : ℂ) (hz : z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) :
      sqrt (z+C.energyShift) ∈ closedBall (c : ℂ) (Real.pi/2) := by
    apply sqrt_mem_closedBall_of_energy_disc c (Real.pi/2) hc
    have hb' : ‖z-(c : ℂ)^2‖ < c*r := by
      simpa only [hcenter,c,mem_ball,dist_eq_norm] using hz
    have hb := hb'.le
    have he : (z+C.energyShift)-(c : ℂ)^2 = (z-(c : ℂ)^2)+C.energyShift := by ring
    have hn := (norm_add_le (z-(c : ℂ)^2) C.energyShift).trans (add_le_add hb hshift)
    rw [← he] at hn
    simp only [mem_closedBall,dist_eq_norm]
    dsimp only [c] at *
    nlinarith [mul_nonneg (show 0 ≤ Real.pi*(n : ℕ) by positivity) (sub_nonneg.mpr hr)]
  let a : ℂ := sqrt (l+C.energyShift)
  let b : ℂ := sqrt (u+C.energyShift)
  have ha : a ∈ closedBall (c : ℂ) (Real.pi/2) := hroot l hpair.left_mem
  have hb : b ∈ closedBall (c : ℂ) (Real.pi/2) := hroot u hpair.right_mem
  have hastrip : a ∈ resonantStrip (n : ℤ) := by
    apply closedBall_subset_resonantStrip (n : ℤ) le_rfl
    simpa only [c,ofReal_mul,ofReal_natCast,Int.cast_natCast] using ha
  have hbstrip : b ∈ resonantStrip (n : ℤ) := by
    apply closedBall_subset_resonantStrip (n : ℤ) le_rfl
    simpa only [c,ofReal_mul,ofReal_natCast,Int.cast_natCast] using hb
  have hac := (hNLS.spectrum_iff a hastrip).mp (C.sqrt_root_mem_periodicSpectrum q hq l hpair.left_zero)
  have hbc := (hNLS.spectrum_iff b hbstrip).mp (C.sqrt_root_mem_periodicSpectrum q hq u hpair.right_zero)
  have hdiff : ‖a-b‖ ≤ ‖x-y‖ := by
    rcases hac with hax | hay <;> rcases hbc with hbx | hby
    · rw [hax,hbx,sub_self,norm_zero]; exact norm_nonneg _
    · rw [hax,hby]
    · rw [hay,hbx,norm_sub_rev]
    · rw [hay,hby,sub_self,norm_zero]; exact norm_nonneg _
  have hsum : ‖a+b‖ ≤ 3*c := by
    have ha' : ‖a-(c : ℂ)‖ ≤ Real.pi/2 := by simpa only [mem_closedBall,dist_eq_norm] using ha
    have hb' : ‖b-(c : ℂ)‖ ≤ Real.pi/2 := by simpa only [mem_closedBall,dist_eq_norm] using hb
    have han := norm_le_norm_sub_add a (c : ℂ)
    have hbn := norm_le_norm_sub_add b (c : ℂ)
    rw [norm_real,Real.norm_of_nonneg hc.le] at han hbn
    have hn := norm_add_le a b
    linarith
  have he : l-u = (a-b)*(a+b) := by
    have hl : a^2 = l+C.energyShift := complex_sqrt_sq _
    have hu : b^2 = u+C.energyShift := complex_sqrt_sq _
    linear_combination -hl+hu
  rw [he,norm_mul]
  calc
    _ ≤ ‖x-y‖*(3*c) := mul_le_mul hdiff hsum (norm_nonneg _) (norm_nonneg _)
    _ = (3*Real.pi)*(n : ℕ)*‖x-y‖ := by dsimp [c]; ring

end NLS.KdV
