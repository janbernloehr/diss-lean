import NLS.ZakharovShabat.QuadraticSpectralBox

/-! # Localization of every real point between the canonical H¹ endpoints -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Endpoint norm bounds control the entire interval between their real parts. -/
theorem abs_sub_re_le_of_mem_endpoint_interval (x y c : ℂ) (r ζ : ℝ)
    (hx : ‖x-c‖ ≤ r) (hy : ‖y-c‖ ≤ r) (hζ : ζ ∈ Set.Icc x.re y.re) :
    |ζ-c.re| ≤ r := by
  have hL := (Complex.abs_re_le_norm (x-c)).trans hx
  have hR := (Complex.abs_re_le_norm (y-c)).trans hy
  simp only [Complex.sub_re,abs_le] at hL hR
  exact abs_le.mpr ⟨by linarith [hζ.1],by linarith [hζ.2]⟩

/-- Every point of a high-index canonical gap has the exact source radius. -/
theorem H1_gap_point_localization
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) (ζ : ℝ)
    (hζ : ζ ∈ Set.Icc
      (canonicalPeriodicLeft (by simp) (by norm_num)
        (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) heven n).re
      (canonicalPeriodicRight (by simp) (by norm_num)
        (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) heven n).re) :
    |ζ-Real.pi*n| ≤ quadraticLocalizationRadius ‖φ‖ n := by
  have h := (H1_periodicSpectrum_uniform_localization φ heven).1 n hn
  have hb := abs_sub_re_le_of_mem_endpoint_interval _ _ ((Real.pi:ℂ)*n) _ ζ h.1 h.2.1 hζ
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.intCast_re,Complex.ofReal_im,
    zero_mul,sub_zero] using hb

/-- Remaining gap points have the central absolute bound required in Proposition 26.1. -/
theorem H1_gap_point_central_bound
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 1+|(n:ℝ)| < 8*‖φ‖^2) (ζ : ℝ)
    (hζ : ζ ∈ Set.Icc
      (canonicalPeriodicLeft (by simp) (by norm_num)
        (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) heven n).re
      (canonicalPeriodicRight (by simp) (by norm_num)
        (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) heven n).re) :
    |ζ| ≤ 8*Real.pi*‖φ‖^2 := by
  have h := H1_canonicalEndpoints_mem_centralBox φ heven n hn
  have hL := (abs_le.mp h.1.1).1
  have hR := (abs_le.mp h.2.1).2
  apply abs_le.mpr
  constructor <;> nlinarith [hζ.1,hζ.2,Real.pi_pos]

end NLS.ZakharovShabat
