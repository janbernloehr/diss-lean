import NLS.KdV.PseudomeasureWideOperatorErrors

/-! The literal shifted-operator estimate for the actual diagonal with
the WEIGHTED potential norm. This variant is distinguished explicitly
from the paper's unweighted right-hand factor in Lemma 2.9(i). -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

theorem wideEndpointDiagonal_opNorm_le_weighted (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 2 ≤ n)
    (z : ℂ) (hz : z ∈ wideHillStrip n) (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) (hq0 : q.val 0=0) :
    ‖endpointDiagonal r hr hr1 n (endpointForgetWeight w r q,z)‖ ≤
      2*wideEndpointShiftedOperatorNorm w r hr hr1 n hn z hz q (-(n:ℤ))*‖q‖ := by
  have h := wideEndpointHillCorrectedMode_coefficient_opNorm_error w r hr hr1 n hn z hz q hs
    (n:ℤ) (n:ℤ) (Or.inl rfl)
  simp only [sub_self,hq0,sub_zero] at h
  have hraw := (wideEndpointCoefficients_eq_weightedCorrectedModes w r hr hr1 n hn z hz q hs).1
  have hw : 1 ≤ w.negativeSobolev r 0 := by
    simpa only [SpectralWeight.negativeSobolev_apply,Weight.sobolev_apply,Int.cast_zero,
      abs_zero,add_zero,Real.one_rpow,div_one] using w.one_le 0
  calc
    _ = ‖(wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs n).val n‖ := congrArg norm hraw
    _ ≤ w.negativeSobolev r 0*‖(wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs n).val n‖ := by
      nlinarith [norm_nonneg ((wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs n).val n)]
    _ ≤ _ := h

end NLS.KdV
