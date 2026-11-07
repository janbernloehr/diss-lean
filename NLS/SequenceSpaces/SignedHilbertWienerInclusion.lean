import NLS.SequenceSpaces.CompactHolderMultiplier
import NLS.SequenceSpaces.SignedSobolevRealScale
import NLS.SequenceSpaces.SobolevEmbedding
import NLS.SequenceSpaces.PeriodOneMassResolvent

/-! One additional signed Hilbert order embeds compactly into the
literal signed Wiener space, at EVERY real order. All raw coefficients,
the physical real form and zero mean are retained. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Weight

theorem signedSobolev_ratio_succ (s : ℝ) (k : ℤ) :
    (signedSobolev s k : ℂ) / (signedSobolev (s + 1) k : ℂ) =
      ((max 1 |(k : ℝ)| : ℝ) : ℂ)⁻¹ := by
  have hb : 0 < max 1 |(k : ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  change (((max 1 |(k : ℝ)|)^s : ℝ) : ℂ) /
    (((max 1 |(k : ℝ)|)^(s + 1) : ℝ) : ℂ) = _
  rw [Real.rpow_add hb, Real.rpow_one, ofReal_mul]
  field_simp [ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hb s).ne', ofReal_ne_zero.mpr hb.ne']

theorem norm_signedSobolev_ratio_succ_le (s : ℝ) (k : ℤ) :
    ‖(signedSobolev s k : ℂ) / (signedSobolev (s + 1) k : ℂ)‖ ≤
      ‖(2 : ℂ) * (sobolev 1 k : ℂ)⁻¹‖ := by
  rw [signedSobolev_ratio_succ]
  have hb : 0 < max 1 |(k : ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc : 0 < 1 + |(k : ℝ)| := by positivity
  have hi : 1 / max 1 |(k : ℝ)| ≤ 2 / (1 + |(k : ℝ)|) := by
    apply (div_le_div_iff₀ hb hc).mpr
    nlinarith [le_max_left (1 : ℝ) |(k : ℝ)|, le_max_right (1 : ℝ) |(k : ℝ)|]
  simp only [norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hb, sobolev_apply, Real.rpow_one, abs_of_pos hc]
  simpa only [one_div, div_eq_mul_inv, one_mul] using hi

theorem memlp_signedSobolev_ratio_succ (s : ℝ) :
    Memℓp (fun k => (signedSobolev s k : ℂ) / (signedSobolev (s + 1) k : ℂ)) 2 := by
  apply ((lp.memℓp NLS.inverseBracketCoefficients).norm.const_mul (2 : ℝ)).mono
  intro k
  change ‖(signedSobolev s k : ℂ) / (signedSobolev (s + 1) k : ℂ)‖ ≤
    2 * ‖NLS.inverseBracketCoefficients k‖
  simpa only [norm_mul, Complex.norm_ofNat, NLS.inverseBracketCoefficients] using!
    norm_signedSobolev_ratio_succ_le s k

end NLS.Weight
namespace NLS.WeightedCoeff

def signedHilbertWienerInclusion (s : ℝ) :
    WeightedCoeff (Weight.signedSobolev (s + 1)) 2 →L[ℂ]
      WeightedCoeff (Weight.signedSobolev s) 1 :=
  weightedHilbertWienerInclusion _ _ (Weight.memlp_signedSobolev_ratio_succ s)

theorem signedHilbertWienerInclusion_apply (s : ℝ)
    (a : WeightedCoeff (Weight.signedSobolev (s + 1)) 2) (k : ℤ) :
    (signedHilbertWienerInclusion s a).val k = a.val k :=
  weightedHilbertWienerInclusion_apply _ _ _ a k

theorem isCompactOperator_signedHilbertWienerInclusion (s : ℝ) :
    IsCompactOperator (signedHilbertWienerInclusion s) :=
  isCompactOperator_weightedHilbertWienerInclusion _ _ _

def signedRealHilbertWienerInclusion (s : ℝ) :
    fourierRealZeroSubmodule (Weight.signedSobolev (s + 1)) 2 →L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev s) 1 :=
  (fourierRealZeroFullProjection _ (Weight.signedSobolev_neg s)).comp
    (((signedHilbertWienerInclusion s).restrictScalars ℝ).comp
      (((zeroModeSubmodule (Weight.signedSobolev (s + 1)) 2).subtypeL.restrictScalars ℝ).comp
        (fourierRealZeroSubmodule (Weight.signedSobolev (s + 1)) 2).subtypeL))

theorem signedRealHilbertWienerInclusion_apply (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (s + 1)) 2) (k : ℤ) :
    (signedRealHilbertWienerInclusion s a).val.val.val k = a.val.val.val k := by
  let b := signedHilbertWienerInclusion s a.val.val
  have hb (j : ℤ) : b.val j = a.val.val.val j := signedHilbertWienerInclusion_apply s a.val.val j
  have h0 : b.val 0 = 0 := (hb 0).trans a.val.property
  have hr (j : ℤ) : b.val (-j) = (starRingEnd ℂ) (b.val j) := by
    rw [hb, hb]
    exact a.property j
  have he := fourierRealZeroFullProjection_inclusion _ (Weight.signedSobolev_neg s)
    (⟨⟨b,h0⟩,hr⟩ : fourierRealZeroSubmodule (Weight.signedSobolev s) 1)
  change (fourierRealZeroFullProjection _ _ b).val.val.val k = _
  rw [he]
  exact hb k

theorem isCompactOperator_signedRealHilbertWienerInclusion (s : ℝ) :
    IsCompactOperator (signedRealHilbertWienerInclusion s) := by
  have hc : IsCompactOperator ((signedHilbertWienerInclusion s).restrictScalars ℝ) :=
    isCompactOperator_signedHilbertWienerInclusion s
  exact (hc.comp_clm _).clm_comp (fourierRealZeroFullProjection _ (Weight.signedSobolev_neg s))

end NLS.WeightedCoeff
