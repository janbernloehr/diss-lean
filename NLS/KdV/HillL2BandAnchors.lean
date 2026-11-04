import NLS.KdV.HillL2BandPhase
import NLS.ComplexAnalysis.ImaginaryCoshInverse
import NLS.KdV.HillL2DiscAsymptotics
import NLS.ZakharovShabat.FreeCosineZeroAudit

/-! # Actual Hill phase anchors at the free cosine zeros

The high free band centers lie in the corresponding actual open bands.
The full indexed band phase then gives a quantitative inverse estimate.
The existing L2 discriminant asymptotics force the actual phase correction
to vanish along these anchors, fixing its branch without a smoothness input.
-/

noncomputable section
open scoped ENNReal
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

def hillFreeBandFrequency (n : ℕ) : ℝ := Real.pi * ((n : ℝ)+1/2)

theorem ofReal_hillFreeBandFrequency (n : ℕ) :
    (hillFreeBandFrequency n : ℂ) = freeCosineZero n := by
  simp [hillFreeBandFrequency, freeCosineZero]

theorem cos_hillFreeBandFrequency (n : ℕ) : Real.cos (hillFreeBandFrequency n) = 0 := by
  rw [show hillFreeBandFrequency n = (n : ℝ)*Real.pi+Real.pi/2 by dsimp [hillFreeBandFrequency]; ring]
  rw [Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]

theorem hillFreeBandFrequency_sq_mem_band
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    (hillFreeBandFrequency n)^2 ∈
      Ioo (hillRealLabels q hq hr (2*n)) (hillRealLabels q hq hr (2*n+1)) := by
  obtain ⟨p, _, hu⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  obtain ⟨s, hl, _⟩ := hillRealLabels_high_pair q hq hr (n+1) (by omega)
    (by push_cast; linarith)
  have hp := (abs_le.mp (p.localization q hq n (by omega) hcut).2).2
  have hs := (abs_le.mp (s.localization q hq (n+1) (by omega) (by push_cast; linarith)).1).1
  rw [show 2*(n+1)-1 = 2*n+1 by omega] at hl
  rw [hu, hl]
  have hnreal : (0 : ℝ) ≤ n := by positivity
  have hπ : 1 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hd₁ : (hillFreeBandFrequency n)^2 - freeHillValue n =
      Real.pi^2*((n : ℝ)+1/4) := by simp only [hillFreeBandFrequency, freeHillValue, Int.cast_natCast]; ring
  have hd₂ : freeHillValue ((n+1 : ℕ) : ℤ) - (hillFreeBandFrequency n)^2 =
      Real.pi^2*((n : ℝ)+3/4) := by
    dsimp only [hillFreeBandFrequency, freeHillValue]
    push_cast
    ring
  have hg₁ : (n : ℝ) < Real.pi^2*((n : ℝ)+1/4) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hπ.le) (show 0 ≤ (n : ℝ)+1/4 by positivity)]
  have hg₂ : (n : ℝ) < Real.pi^2*((n : ℝ)+3/4) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hπ.le) (show 0 ≤ (n : ℝ)+3/4 by positivity)]
  constructor <;> linarith

theorem hillL2UpperBoundaryPrimitive_midphase_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2*n)) (hillRealLabels q hq hr (2*n+1))) :
    ‖hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x + I*(hillFreeBandFrequency n)‖ ≤
      Real.pi/4 * ‖hillL2Discriminant (SpectralWeight.one.toCoeff q) x‖ := by
  let B := hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x
  let u := B + I*(hillFreeBandFrequency n)
  have hre : B.re = 0 := hillL2UpperBoundaryPrimitive_re_eq_zero_band q hq hr n x hx
  have hphase := hillL2UpperBoundaryPrimitive_band_phase q hq hr n x hx
  have hstrip : |u.im| ≤ Real.pi/2 := by
    rw [abs_le]
    dsimp [u, B, hillFreeBandFrequency]
    simp only [mul_im, I_re, I_im, ofReal_im, ofReal_re, zero_mul, one_mul, zero_add]
    constructor <;> linarith [hphase.1, hphase.2]
  have h := norm_imaginary_phase_le_cosh_shift (hillFreeBandFrequency n)
    (cos_hillFreeBandFrequency n) u (by dsimp [u]; simp [hre]) hstrip
  have he : -I*(hillFreeBandFrequency n)+u = B := by dsimp [u]; ring
  rw [he] at h
  have ht : 2*cosh B = hillL2Discriminant (SpectralWeight.one.toCoeff q) x := by
    simpa only [hillL2RealCutPrimitive, ofReal_im, if_true, ofReal_re, B] using
      hillL2RealCutPrimitive_trace q hq hr (x : ℂ)
  simpa only [B, u, ht] using h

theorem tendsto_hillL2Discriminant_freeCosineZero (q : Coeff 2) :
    Tendsto (fun n => hillL2Discriminant q ((freeCosineZero n)^2)) atTop (𝓝 0) := by
  have h := tendsto_discriminant_error_of_potential_tendsto
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞))
    (fun _ : ℕ => hillL2CoefficientPotential q) tendsto_const_nhds
    (fun _ => hillL2CoefficientPotential_even q) freeCosineZero tendsto_norm_freeCosineZero
    (by positivity : 0 < Real.pi/4) le_rfl freeCosineZero_separated
  simpa only [canonicalDiscriminant_hillL2CoefficientPotential, freeDiscriminant_freeCosineZero,
    sub_zero, freeCosineZero_im, abs_zero, Real.exp_zero, ofReal_one, div_one] using h

theorem tendsto_hillL2RealCutPrimitive_free_band_correction
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    Tendsto (fun n => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) ((freeCosineZero n)^2) +
      I*freeCosineZero n) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_nat_ge (8*‖q‖)
  have hb : ∀ᶠ n : ℕ in atTop,
      ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) ((freeCosineZero n)^2) + I*freeCosineZero n‖ ≤
        Real.pi/4 * ‖hillL2Discriminant (SpectralWeight.one.toCoeff q) ((freeCosineZero n)^2)‖ := by
    filter_upwards [eventually_ge_atTop (max 2 K)] with n hn
    have hcut : 8*‖q‖ ≤ (n : ℝ) := hK.trans (by exact_mod_cast (show K ≤ n by omega))
    have h := hillL2UpperBoundaryPrimitive_midphase_bound q hq hr n ((hillFreeBandFrequency n)^2)
      (hillFreeBandFrequency_sq_mem_band q hq hr n (by omega) hcut)
    rw [← ofReal_hillFreeBandFrequency]
    simpa only [← ofReal_pow, hillL2RealCutPrimitive, ofReal_im, if_true, ofReal_re] using h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hb
  simpa only [norm_zero, mul_zero] using
    (tendsto_hillL2Discriminant_freeCosineZero (SpectralWeight.one.toCoeff q)).norm.const_mul (Real.pi/4)

end NLS.KdV
