import NLS.KdV.PseudomeasureWideWeightedErrors

/-! Errors measured by the literal shifted operator norm of the original
wide-strip convolution operator, rather than by its explicit majorant. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- The source shifted operator norm is the norm of conjugation by the
coefficient-preserving equivalence defining that shifted norm. -/
def wideEndpointShiftedOperatorNorm (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r)
    (hr1 : r < 1/2) (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) (i : ℤ) : ℝ :=
  ‖(w.negativeShiftEquiv r hr i ⊤).toContinuousLinearMap.comp
    ((wideEndpointHillPerturbation w r hr hr1 n hn z hz q).comp
      (w.negativeShiftEquiv r hr i ⊤).symm.toContinuousLinearMap)‖

theorem negativeShiftedNorm_wideEndpointHillPerturbation_opNorm_le
    (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q a : WeightedCoeff (w.negativeSobolev r) ⊤) (i : ℤ) :
    w.negativeShiftedNorm r hr i ⊤ (wideEndpointHillPerturbation w r hr hr1 n hn z hz q a) ≤
      wideEndpointShiftedOperatorNorm w r hr hr1 n hn z hz q i *
        w.negativeShiftedNorm r hr i ⊤ a := by
  let e := w.negativeShiftEquiv r hr i ⊤
  let T := wideEndpointHillPerturbation w r hr hr1 n hn z hz q
  have h := (e.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap)).le_opNorm (e a)
  change ‖e (T a)‖ ≤ _
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, wideEndpointShiftedOperatorNorm,
    SpectralWeight.negativeShiftedNorm, e, T] using h

variable (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
variable (q : WeightedCoeff (w.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- Every corrected-mode coefficient error has the exact source shifted
operator norm, with no replacement by an a-priori norm bound. -/
theorem wideEndpointHillCorrectedMode_coefficient_opNorm_error (j k : ℤ)
    (hj : j = (n:ℤ) ∨ j = -(n:ℤ)) :
    w.negativeSobolev r (k-j)*
        ‖(wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs j).val k-q.val (k-j)‖ ≤
      2*wideEndpointShiftedOperatorNorm w r hr hr1 n hn z hz q (-j)*‖q‖ := by
  let a := wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs j
  have hInv := wideEndpointHillTailInverse_right w r hr hr1 n hn z hz q hs
    (w.negativeModulation r hr j q)
  have he : a-w.negativeModulation r hr j q =
      wideEndpointHillPerturbation w r hr hr1 n hn z hz q a := by
    change a-wideEndpointHillPerturbation w r hr hr1 n hn z hz q a =
      w.negativeModulation r hr j q at hInv
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hInv).trans (add_comm _ _))
  calc
    _ = w.negativeSobolev r (k-j)*‖(a-w.negativeModulation r hr j q).val k‖ := by
      rw [WeightedCoeff.sub_val, SpectralWeight.negativeModulation_apply]
    _ ≤ w.negativeShiftedNorm r hr (-j) ⊤ (a-w.negativeModulation r hr j q) := by
      simpa only [sub_eq_add_neg] using negativeShiftedNorm_coefficient_le w r hr (-j) k _
    _ ≤ wideEndpointShiftedOperatorNorm w r hr hr1 n hn z hz q (-j)*
        w.negativeShiftedNorm r hr (-j) ⊤ a := by
      rw [he]
      exact negativeShiftedNorm_wideEndpointHillPerturbation_opNorm_le w r hr hr1 n hn z hz q a (-j)
    _ ≤ wideEndpointShiftedOperatorNorm w r hr hr1 n hn z hz q (-j)*(2*‖q‖) := by
      apply mul_le_mul_of_nonneg_left
        (negativeShiftedNorm_wideEndpointHillCorrectedMode_le w r hr hr1 n hn z hz q hs j hj)
      exact norm_nonneg _
    _ = _ := by ring

include hs in
/-- Both physical off-diagonal entries satisfy the literal operator-norm
inequalities of Lemma 2.9(ii) on the entire printed strip. -/
theorem wideEndpointCouplings_opNorm_errors :
    w.negativeSobolev r (2*(n:ℤ))*
        ‖endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)-q.val (2*(n:ℤ))‖ ≤
      2*wideEndpointShiftedOperatorNorm w r hr hr1 n hn z hz q (n:ℤ)*‖q‖ ∧
    w.negativeSobolev r (2*(n:ℤ))*
        ‖endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)-q.val (-(2*(n:ℤ)))‖ ≤
      2*wideEndpointShiftedOperatorNorm w r hr hr1 n hn z hz q (-(n:ℤ))*‖q‖ := by
  obtain ⟨_,hb,hc⟩ := wideEndpointCoefficients_eq_weightedCorrectedModes w r hr hr1 n hn z hz q hs
  rw [hb,hc]
  constructor
  · simpa only [neg_neg, show (n:ℤ)- -(n:ℤ)=2*(n:ℤ) by ring] using
      wideEndpointHillCorrectedMode_coefficient_opNorm_error w r hr hr1 n hn z hz q hs
        (-(n:ℤ)) n (Or.inr rfl)
  · simpa only [show -(n:ℤ)-(n:ℤ)= -(2*(n:ℤ)) by ring, SpectralWeight.negativeSobolev_neg] using
      wideEndpointHillCorrectedMode_coefficient_opNorm_error w r hr hr1 n hn z hz q hs
        n (-(n:ℤ)) (Or.inl rfl)

end NLS.KdV
