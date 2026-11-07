import NLS.KdV.HillWideDiagonalWeightedOperatorBound
import NLS.KdV.PseudomeasureWideBilinearSymmetry

/-! The repaired diagonal estimate holds in BOTH literal opposite
shifted operator norms on the full printed strip. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
variable (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
variable (q : WeightedCoeff (w.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

theorem wideEndpointDiagonal_eq_negativeCorrectedMode :
    endpointDiagonal r hr hr1 n (endpointForgetWeight w r q,z) =
      (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs (-(n:ℤ))).val (-(n:ℤ)) := by
  have hv := wideEndpointHill_small_forgetWeight w r hr1 n q hs
  unfold endpointDiagonal
  rw [endpointEffectiveFamily_eq_wide r hr hr1 n hn (endpointForgetWeight w r q,z) hz hv,
    wideEndpointHillEffectivePotential_diagonals_eq r hr hr1 n hn z hz _ hv,
    ← wideEndpointHillCorrectedMode_neg r hr hr1 n hn z hz _ hv]
  exact (wideEndpointHillCorrectedMode_forgetWeight_coefficient w r hr hr1 n hn z hz q hs hv
    (-(n:ℤ)) (-(n:ℤ))).symm

include hs in
theorem wideEndpointDiagonal_opNorm_le_weighted_opposite (hq0 : q.val 0=0) :
    ‖endpointDiagonal r hr hr1 n (endpointForgetWeight w r q,z)‖ ≤
      2*wideEndpointShiftedOperatorNorm w r hr hr1 n hn z hz q (n:ℤ)*‖q‖ := by
  have h := wideEndpointHillCorrectedMode_coefficient_opNorm_error w r hr hr1 n hn z hz q hs
    (-(n:ℤ)) (-(n:ℤ)) (Or.inr rfl)
  simp only [sub_self,hq0,sub_zero,neg_neg] at h
  have hw : 1 ≤ w.negativeSobolev r 0 := by
    simpa only [SpectralWeight.negativeSobolev_apply,Weight.sobolev_apply,Int.cast_zero,
      abs_zero,add_zero,Real.one_rpow,div_one] using w.one_le 0
  rw [wideEndpointDiagonal_eq_negativeCorrectedMode w r hr hr1 n hn z hz q hs]
  calc
    _ ≤ w.negativeSobolev r 0*
        ‖(wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs (-(n:ℤ))).val (-(n:ℤ))‖ := by
      nlinarith [norm_nonneg ((wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs
        (-(n:ℤ))).val (-(n:ℤ)))]
    _ ≤ _ := h

end NLS.KdV
