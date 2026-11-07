import NLS.KdV.PseudomeasureCoefficients
import NLS.KdV.HillComplement
import NLS.SequenceSpaces.PositiveConvolutionEnvelope

/-! Shift and weight the actual Hill tail operator around its forcing
mode. The normalized matrix retains the original reciprocal symbol. -/
noncomputable section
open scoped ENNReal
open NLS.WeightedCoeff
namespace NLS.KdV

def hillWienerNormalize (w : SpectralWeight) (j : ℤ) :
    WeightedCoeff (w.negativeSobolev 0) ⊤ ≃L[ℂ] Coeff ⊤ :=
  (w.negativeModulation 0 (by norm_num) (-j)).trans
    (weightIsometry (w.negativeSobolev 0) ⊤).toContinuousLinearEquiv

theorem hillWienerNormalize_apply (w : SpectralWeight) (j : ℤ)
    (a : WeightedCoeff (w.negativeSobolev 0) ⊤) (k : ℤ) :
    hillWienerNormalize w j a k = (w k:ℂ)*a.val (k+j) := by
  change (w.negativeSobolev 0 k:ℂ)*(w.negativeModulation 0 (by norm_num) (-j) a).val k = _
  rw [SpectralWeight.negativeModulation_apply]
  simp only [SpectralWeight.negativeSobolev_apply, Weight.sobolev_zero_apply, div_one,
    sub_neg_eq_add]

theorem hillWienerNormalize_symm_apply (w : SpectralWeight) (j : ℤ) (f : Coeff ⊤) (k : ℤ) :
    ((hillWienerNormalize w j).symm f).val k = f (k-j)/(w (k-j):ℂ) := by
  have h := congrArg (fun a : Coeff ⊤ => a (k-j)) ((hillWienerNormalize w j).apply_symm_apply f)
  rw [hillWienerNormalize_apply, sub_add_cancel] at h
  exact (eq_div_iff (w.toWeight.complex_ne_zero (k-j))).mpr ((mul_comm _ _).trans h)

theorem hillWienerNormalize_modulation (w : SpectralWeight) (j : ℤ)
    (q : WeightedCoeff (w.negativeSobolev 0) ⊤) (k : ℤ) :
    hillWienerNormalize w j (w.negativeModulation 0 (by norm_num) j q) k = (w k:ℂ)*q.val k := by
  rw [hillWienerNormalize_apply, SpectralWeight.negativeModulation_apply, add_sub_cancel_right]

theorem norm_hillWienerNormalize (w : SpectralWeight) (j : ℤ)
    (a : WeightedCoeff (w.negativeSobolev 0) ⊤) :
    ‖hillWienerNormalize w j a‖ = w.negativeShiftedNorm 0 (by norm_num) (-j) ⊤ a := by
  change ‖(weightIsometry (w.negativeSobolev 0) ⊤)
    (w.negativeModulation 0 (by norm_num) (-j) a)‖ = _
  rw [LinearIsometryEquiv.norm_map]
  change ‖WeightedCoeff.shiftWeightIsometry (w.negativeSobolev 0) (-j)
    (w.negativeShiftEquiv 0 (by norm_num) (-j) ⊤ a)‖ = _
  rw [LinearIsometryEquiv.norm_map]
  rfl

def hillWienerNormalizedTail (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev 0) ⊤) (j : ℤ) : Coeff ⊤ →L[ℂ] Coeff ⊤ :=
  (hillWienerNormalize w j).conjContinuousAlgEquiv
    (unshiftedEndpointHillPerturbation w 0 (by norm_num) (by norm_num) n hn z hz q)

theorem hillWienerNormalizedTail_apply (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev 0) ⊤) (j : ℤ) (f : Coeff ⊤) (m : ℤ) :
    hillWienerNormalizedTail w n hn z hz q j f m = ∑' k : ℤ,
      (w m:ℂ)*q.val (m-k)*reducedHillSymbol n hn z hz (k+j)*f k/(w k:ℂ) := by
  change hillWienerNormalize w j (unshiftedEndpointHillPerturbation w 0 (by norm_num)
    (by norm_num) n hn z hz q ((hillWienerNormalize w j).symm f)) m = _
  rw [hillWienerNormalize_apply, unshiftedEndpointHillPerturbation_apply, ← tsum_mul_left,
    ← (Equiv.addRight j).tsum_eq (fun k : ℤ =>
      (w m:ℂ)*(q.val (m+j-k)*reducedHillSymbol n hn z hz k*
        ((hillWienerNormalize w j).symm f).val k))]
  apply tsum_congr
  intro k
  change (w m:ℂ)*(q.val (m+j-(k+j))*reducedHillSymbol n hn z hz (k+j)*
    ((hillWienerNormalize w j).symm f).val (k+j)) = _
  rw [hillWienerNormalize_symm_apply]
  simp only [add_sub_add_right_eq_sub, add_sub_cancel_right]
  ring

theorem norm_hillWienerNormalizedTail_le (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev 0) ⊤) (j : ℤ)
    (hj : j=(n:ℤ) ∨ j=-(n:ℤ)) :
    ‖hillWienerNormalizedTail w n hn z hz q j‖ ≤
      endpointHillConstant 0*(n:ℝ)^((0:ℝ)-1/2)*‖q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [endpointHillConstant_pos 0 (by norm_num)])
  intro f
  let a := (hillWienerNormalize w j).symm f
  have h := negativeShiftedNorm_endpointHillPerturbation_le w 0 (by norm_num) (by norm_num)
    n hn z hz q a
  have hh : w.negativeShiftedNorm 0 (by norm_num) (-j) ⊤
      (unshiftedEndpointHillPerturbation w 0 (by norm_num) (by norm_num) n hn z hz q a) ≤
        endpointHillConstant 0*(n:ℝ)^((0:ℝ)-1/2)*‖q‖*w.negativeShiftedNorm 0 (by norm_num) (-j) ⊤ a := by
    rcases hj with rfl | rfl
    · exact h.2
    · simpa only [neg_neg] using h.1
  rw [← norm_hillWienerNormalize, ← norm_hillWienerNormalize] at hh
  change ‖hillWienerNormalize w j (unshiftedEndpointHillPerturbation w 0 (by norm_num)
    (by norm_num) n hn z hz q ((hillWienerNormalize w j).symm f))‖ ≤ _
  simpa only [a, ContinuousLinearEquiv.apply_symm_apply] using hh

end NLS.KdV
