import NLS.KdV.PseudomeasureWideCouplingRadius
import NLS.KdV.PseudomeasureWeightedCoefficients

/-! Corrected resonant modes and arbitrary-weight errors for the same
physical Hill operator on the full printed strip. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

variable (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
variable (q : WeightedCoeff (w.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- The corrected potential of an actual signed Fourier unit mode. -/
def wideEndpointHillCorrectedMode (j : ℤ) : WeightedCoeff (w.negativeSobolev r) ⊤ :=
  wideEndpointHillTailInverse w r hr hr1 n hn z hz q hs (w.negativeModulation r hr j q)

/-- Its opposite shifted norm has the bound two at either resonant frequency. -/
theorem negativeShiftedNorm_wideEndpointHillCorrectedMode_le (j : ℤ)
    (hj : j = (n:ℤ) ∨ j = -(n:ℤ)) :
    w.negativeShiftedNorm r hr (-j) ⊤
      (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs j) ≤ 2*‖q‖ := by
  have h := negativeShiftedNorm_wideEndpointHillTailInverse_le w r hr hr1 n hn z hz q hs
    (w.negativeModulation r hr j q)
  have hnorm := w.negativeShiftedNorm_negativeModulation r hr j q
  rcases hj with rfl | rfl
  · simpa only [wideEndpointHillCorrectedMode, hnorm] using h.2
  · simp only [neg_neg] at hnorm
    simpa only [wideEndpointHillCorrectedMode, neg_neg, hnorm] using h.1

/-- Weighted endpoint error at every coefficient of either corrected resonant mode. -/
theorem wideEndpointHillCorrectedMode_coefficient_error (j k : ℤ)
    (hj : j = (n:ℤ) ∨ j = -(n:ℤ)) :
    w.negativeSobolev r (k-j)*
        ‖(wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs j).val k-q.val (k-j)‖ ≤
      2*(13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ := by
  let a := wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs j
  have hInv := wideEndpointHillTailInverse_right w r hr hr1 n hn z hz q hs
    (w.negativeModulation r hr j q)
  have he : a-w.negativeModulation r hr j q =
      wideEndpointHillPerturbation w r hr hr1 n hn z hz q a := by
    change a-wideEndpointHillPerturbation w r hr hr1 n hn z hz q a =
      w.negativeModulation r hr j q at hInv
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hInv).trans (add_comm _ _))
  have ht : w.negativeShiftedNorm r hr (-j) ⊤
      (wideEndpointHillPerturbation w r hr hr1 n hn z hz q a) ≤
        (13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*w.negativeShiftedNorm r hr (-j) ⊤ a := by
    rcases hj with rfl | rfl
    · exact (negativeShiftedNorm_wideEndpointHillPerturbation_le w r hr hr1 n hn z hz q a).2
    · simpa only [neg_neg] using
        (negativeShiftedNorm_wideEndpointHillPerturbation_le w r hr hr1 n hn z hz q a).1
  calc
    _ = w.negativeSobolev r (k-j)*‖(a-w.negativeModulation r hr j q).val k‖ := by
      rw [WeightedCoeff.sub_val, SpectralWeight.negativeModulation_apply]
    _ ≤ w.negativeShiftedNorm r hr (-j) ⊤ (a-w.negativeModulation r hr j q) := by
      simpa only [sub_eq_add_neg] using negativeShiftedNorm_coefficient_le w r hr (-j) k _
    _ ≤ (13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*w.negativeShiftedNorm r hr (-j) ⊤ a := by
      rw [he]
      exact ht
    _ ≤ (13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(2*‖q‖) := by
      apply mul_le_mul_of_nonneg_left
        (negativeShiftedNorm_wideEndpointHillCorrectedMode_le w r hr hr1 n hn z hz q hs j hj)
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (endpointHillConstant_pos r hr1).le)
        (Real.rpow_nonneg (by positivity) _)) (norm_nonneg q)
    _ = _ := by ring

/-- The first resonant corrected mode is the original physical effective source column. -/
theorem wideEndpointHillCorrectedMode_pos (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    wideEndpointHillCorrectedMode SpectralWeight.one r hr hr1 n hn z hz q hs n =
      wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0) := by
  change wideEndpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
      (SpectralWeight.one.negativeModulation r hr (n:ℤ) q) =
    wideEndpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
      (endpointHillModePotential r hr hr1 n q (1,0))
  rw [endpointHillModePotential_basis_pos]

/-- The second physical effective source column is the opposite corrected mode. -/
theorem wideEndpointHillCorrectedMode_neg (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    wideEndpointHillCorrectedMode SpectralWeight.one r hr hr1 n hn z hz q hs (-(n:ℤ)) =
      wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1) := by
  change wideEndpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
      (SpectralWeight.one.negativeModulation r hr (-(n:ℤ)) q) =
    wideEndpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
      (endpointHillModePotential r hr hr1 n q (0,1))
  rw [endpointHillModePotential_basis_neg]


end NLS.KdV
