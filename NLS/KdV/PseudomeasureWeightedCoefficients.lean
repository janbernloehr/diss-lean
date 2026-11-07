import NLS.KdV.PseudomeasureWeightInclusion

/-! General spectral-weight estimates for the SAME original physical effective coefficients. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- Forget only the extra spectral weight, preserving every original coefficient. -/
def endpointForgetWeight (w : SpectralWeight) (r : ℝ) :
    WeightedCoeff (w.negativeSobolev r) ⊤ →L[ℂ]
      WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  endpointWeightInclusion w SpectralWeight.one (fun k => w.one_le k) r

@[simp] theorem endpointForgetWeight_apply (w : SpectralWeight) (r : ℝ)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) (k : ℤ) :
    (endpointForgetWeight w r q).val k = q.val k :=
  endpointWeightInclusion_apply _ _ _ _ q k

theorem norm_endpointForgetWeight_le (w : SpectralWeight) (r : ℝ)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) : ‖endpointForgetWeight w r q‖ ≤ ‖q‖ :=
  norm_endpointWeightInclusion_le _ _ _ _ q

theorem endpointHill_small_forgetWeight (w : SpectralWeight) (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    endpointHillConstant r*(n:ℝ)^(r-1/2)*‖endpointForgetWeight w r q‖ ≤ 1/2 :=
  endpointHill_small_weightInclusion _ _ _ r hr1 n q hs

variable (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
variable (q : WeightedCoeff (w.negativeSobolev r) ⊤)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- Weighted corrected modes have exactly the already verified physical unit-weight coefficients. -/
theorem endpointHillCorrectedMode_forgetWeight_coefficient
    (hv : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖endpointForgetWeight w r q‖ ≤ 1/2) (j k : ℤ) :
    (endpointHillCorrectedMode w r hr hr1 n hn z hz q hs j).val k =
      (endpointHillCorrectedMode SpectralWeight.one r hr hr1 n hn z hz
        (endpointForgetWeight w r q) hv j).val k := by
  have he := congrArg (fun a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ => a.val k)
    (endpointHillCorrectedMode_weightInclusion w SpectralWeight.one (fun k => w.one_le k)
      r hr hr1 n hn z hz q hs hv j)
  exact (endpointWeightInclusion_apply w SpectralWeight.one (fun k => w.one_le k) r
    (endpointHillCorrectedMode w r hr hr1 n hn z hz q hs j) k).symm.trans he

/-- All three actual physical entries are literal weighted corrected-mode coefficients. -/
theorem endpointCoefficients_eq_weightedCorrectedModes :
    endpointDiagonal r hr hr1 n (endpointForgetWeight w r q,z) =
        (endpointHillCorrectedMode w r hr hr1 n hn z hz q hs n).val n ∧
      endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z) =
        (endpointHillCorrectedMode w r hr hr1 n hn z hz q hs (-(n:ℤ))).val n ∧
      endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z) =
        (endpointHillCorrectedMode w r hr hr1 n hn z hz q hs n).val (-(n:ℤ)) := by
  have hv := endpointHill_small_forgetWeight w r hr1 n q hs
  unfold endpointDiagonal endpointUpperCoupling endpointLowerCoupling
  rw [endpointEffectiveFamily_eq r hr hr1 n hn (endpointForgetWeight w r q,z) hz hv]
  rw [← endpointHillCorrectedMode_pos r hr hr1 n hn z hz _ hv,
    ← endpointHillCorrectedMode_neg r hr hr1 n hn z hz _ hv]
  exact ⟨(endpointHillCorrectedMode_forgetWeight_coefficient w r hr hr1 n hn z hz q hs hv n n).symm,
    (endpointHillCorrectedMode_forgetWeight_coefficient w r hr hr1 n hn z hz q hs hv (-(n:ℤ)) n).symm,
    (endpointHillCorrectedMode_forgetWeight_coefficient w r hr hr1 n hn z hz q hs hv n (-(n:ℤ))).symm⟩

include hn hz hs in
/-- Full-strip diagonal and coupling errors in EVERY source spectral weight,
for the original physical entries rather than a replacement characteristic. -/
theorem endpointCoefficients_weighted_errors_le :
    w.negativeSobolev r 0*‖endpointDiagonal r hr hr1 n (endpointForgetWeight w r q,z)-q.val 0‖ ≤
        2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ ∧
      w.negativeSobolev r (2*(n:ℤ))*‖endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)-q.val (2*(n:ℤ))‖ ≤
        2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ ∧
      w.negativeSobolev r (2*(n:ℤ))*‖endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)-q.val (-(2*(n:ℤ)))‖ ≤
        2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ := by
  obtain ⟨ha, hb, hc⟩ := endpointCoefficients_eq_weightedCorrectedModes w r hr hr1 n hn z hz q hs
  rw [ha, hb, hc]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [sub_self] using
      endpointHillCorrectedMode_coefficient_error w r hr hr1 n hn z hz q hs n n (Or.inl rfl)
  · simpa only [show (n:ℤ)- -(n:ℤ) = 2*(n:ℤ) by ring] using
      endpointHillCorrectedMode_coefficient_error w r hr hr1 n hn z hz q hs (-(n:ℤ)) n (Or.inr rfl)
  · simpa only [show -(n:ℤ)-(n:ℤ) = -(2*(n:ℤ)) by ring, SpectralWeight.negativeSobolev_neg] using
      endpointHillCorrectedMode_coefficient_error w r hr hr1 n hn z hz q hs n (-(n:ℤ)) (Or.inl rfl)

include hn hz hs in
/-- Both actual couplings retain their exact weighted endpoint size on the full strip. -/
theorem endpointCouplings_weighted_le :
    w.negativeSobolev r (2*(n:ℤ))*‖endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)‖ ≤ 2*‖q‖ ∧
      w.negativeSobolev r (2*(n:ℤ))*‖endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)‖ ≤ 2*‖q‖ := by
  obtain ⟨_, hb, hc⟩ := endpointCoefficients_eq_weightedCorrectedModes w r hr hr1 n hn z hz q hs
  rw [hb, hc]
  constructor
  · have hbound : w.negativeShiftedNorm r hr (n:ℤ) ⊤
        (endpointHillCorrectedMode w r hr hr1 n hn z hz q hs (-(n:ℤ))) ≤ 2*‖q‖ := by
      simpa only [neg_neg] using
        negativeShiftedNorm_endpointHillCorrectedMode_le w r hr hr1 n hn z hz q hs (-(n:ℤ)) (Or.inr rfl)
    have h := (negativeShiftedNorm_coefficient_le w r hr (n:ℤ) n
      (endpointHillCorrectedMode w r hr hr1 n hn z hz q hs (-(n:ℤ)))).trans
      hbound
    simpa only [show (n:ℤ)+(n:ℤ) = 2*(n:ℤ) by ring] using h
  · have h := (negativeShiftedNorm_coefficient_le w r hr (-(n:ℤ)) (-(n:ℤ))
      (endpointHillCorrectedMode w r hr hr1 n hn z hz q hs n)).trans
      (negativeShiftedNorm_endpointHillCorrectedMode_le w r hr hr1 n hn z hz q hs n (Or.inl rfl))
    simpa only [show -(n:ℤ)+ -(n:ℤ) = -(2*(n:ℤ)) by ring, SpectralWeight.negativeSobolev_neg] using h

end NLS.KdV
