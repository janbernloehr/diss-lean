import NLS.KdV.PseudomeasureWideWeightInclusion

/-! Weighted wide-strip errors for the original physical coefficients.
No weighted determinant is substituted for the physical one. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

theorem wideEndpointHill_small_forgetWeight (w : SpectralWeight) (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖endpointForgetWeight w r q‖ ≤ 1/2 :=
  wideEndpointHill_small_weightInclusion _ _ _ r hr1 n q hs

variable (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
variable (q : WeightedCoeff (w.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- Weighted corrected modes have exactly the already verified physical unit-weight coefficients. -/
theorem wideEndpointHillCorrectedMode_forgetWeight_coefficient
    (hv : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖endpointForgetWeight w r q‖ ≤ 1/2) (j k : ℤ) :
    (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs j).val k =
      (wideEndpointHillCorrectedMode SpectralWeight.one r hr hr1 n hn z hz
        (endpointForgetWeight w r q) hv j).val k := by
  have he := congrArg (fun a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ => a.val k)
    (wideEndpointHillCorrectedMode_weightInclusion w SpectralWeight.one (fun k => w.one_le k)
      r hr hr1 n hn z hz q hs hv j)
  exact (endpointWeightInclusion_apply w SpectralWeight.one (fun k => w.one_le k) r
    (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs j) k).symm.trans he

/-- All three actual physical entries are literal weighted corrected-mode coefficients. -/
theorem wideEndpointCoefficients_eq_weightedCorrectedModes :
    endpointDiagonal r hr hr1 n (endpointForgetWeight w r q,z) =
        (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs n).val n ∧
      endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z) =
        (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs (-(n:ℤ))).val n ∧
      endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z) =
        (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs n).val (-(n:ℤ)) := by
  have hv := wideEndpointHill_small_forgetWeight w r hr1 n q hs
  unfold endpointDiagonal endpointUpperCoupling endpointLowerCoupling
  rw [endpointEffectiveFamily_eq_wide r hr hr1 n hn (endpointForgetWeight w r q,z) hz hv]
  rw [← wideEndpointHillCorrectedMode_pos r hr hr1 n hn z hz _ hv,
    ← wideEndpointHillCorrectedMode_neg r hr hr1 n hn z hz _ hv]
  exact ⟨(wideEndpointHillCorrectedMode_forgetWeight_coefficient w r hr hr1 n hn z hz q hs hv n n).symm,
    (wideEndpointHillCorrectedMode_forgetWeight_coefficient w r hr hr1 n hn z hz q hs hv (-(n:ℤ)) n).symm,
    (wideEndpointHillCorrectedMode_forgetWeight_coefficient w r hr hr1 n hn z hz q hs hv n (-(n:ℤ))).symm⟩

include hn hz hs in
/-- Full-strip diagonal and coupling errors in EVERY source spectral weight,
for the original physical entries rather than a replacement characteristic. -/
theorem wideEndpointCoefficients_weighted_errors_le :
    w.negativeSobolev r 0*‖endpointDiagonal r hr hr1 n (endpointForgetWeight w r q,z)-q.val 0‖ ≤
        2*(13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ ∧
      w.negativeSobolev r (2*(n:ℤ))*‖endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)-q.val (2*(n:ℤ))‖ ≤
        2*(13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ ∧
      w.negativeSobolev r (2*(n:ℤ))*‖endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)-q.val (-(2*(n:ℤ)))‖ ≤
        2*(13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ := by
  obtain ⟨ha, hb, hc⟩ := wideEndpointCoefficients_eq_weightedCorrectedModes w r hr hr1 n hn z hz q hs
  rw [ha, hb, hc]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [sub_self] using
      wideEndpointHillCorrectedMode_coefficient_error w r hr hr1 n hn z hz q hs n n (Or.inl rfl)
  · simpa only [show (n:ℤ)- -(n:ℤ) = 2*(n:ℤ) by ring] using
      wideEndpointHillCorrectedMode_coefficient_error w r hr hr1 n hn z hz q hs (-(n:ℤ)) n (Or.inr rfl)
  · simpa only [show -(n:ℤ)-(n:ℤ) = -(2*(n:ℤ)) by ring, SpectralWeight.negativeSobolev_neg] using
      wideEndpointHillCorrectedMode_coefficient_error w r hr hr1 n hn z hz q hs n (-(n:ℤ)) (Or.inl rfl)

include hn hz hs in
/-- Both actual couplings retain their exact weighted endpoint size on the full strip. -/
theorem wideEndpointCouplings_weighted_le :
    w.negativeSobolev r (2*(n:ℤ))*‖endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)‖ ≤ 2*‖q‖ ∧
      w.negativeSobolev r (2*(n:ℤ))*‖endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)‖ ≤ 2*‖q‖ := by
  obtain ⟨_, hb, hc⟩ := wideEndpointCoefficients_eq_weightedCorrectedModes w r hr hr1 n hn z hz q hs
  rw [hb, hc]
  constructor
  · have hbound : w.negativeShiftedNorm r hr (n:ℤ) ⊤
        (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs (-(n:ℤ))) ≤ 2*‖q‖ := by
      simpa only [neg_neg] using
        negativeShiftedNorm_wideEndpointHillCorrectedMode_le w r hr hr1 n hn z hz q hs (-(n:ℤ)) (Or.inr rfl)
    have h := (negativeShiftedNorm_coefficient_le w r hr (n:ℤ) n
      (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs (-(n:ℤ)))).trans
      hbound
    simpa only [show (n:ℤ)+(n:ℤ) = 2*(n:ℤ) by ring] using h
  · have h := (negativeShiftedNorm_coefficient_le w r hr (-(n:ℤ)) (-(n:ℤ))
      (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs n)).trans
      (negativeShiftedNorm_wideEndpointHillCorrectedMode_le w r hr hr1 n hn z hz q hs n (Or.inl rfl))
    simpa only [show -(n:ℤ)+ -(n:ℤ) = -(2*(n:ℤ)) by ring, SpectralWeight.negativeSobolev_neg] using h

end NLS.KdV
