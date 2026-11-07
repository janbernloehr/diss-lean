import NLS.SequenceSpaces.SignedSobolevConvolution
import NLS.SequenceSpaces.HolderEmbedding

/-! The mixed endpoint estimate of Appendix A.3(ii), with the literal
Sobolev weights, an absolutely convergent convolution at every mode, and
a constant independent of the two input sequences. -/
noncomputable section
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open WeightedCoeff

private theorem weight_eq_of_apply_eq (w v : Weight) (h : ∀ k, w k=v k) : w=v := by
  cases w with
  | mk wf hw =>
    cases v with
    | mk vf hv =>
      have he : wf=vf := funext h
      cases he
      rfl

/-- Appendix A.3(ii), including the endpoint s=-1/2. -/
theorem sourceLemmaA_3_ii (s t : ℝ) (_hs : -(1:ℝ)/2 ≤ s) (hs0 : s ≤ 0)
    (hst : -s-3/2 < t) (_ht : t < 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : WeightedCoeff (Weight.sobolev s) ⊤,
      ∀ b : WeightedCoeff (Weight.sobolev (t+2)) 2,
      ∃ c : WeightedCoeff (Weight.sobolev s) ⊤,
        (∀ n : ℤ, Summable (fun k : ℤ => a.val (n-k)*b.val k) ∧
          c.val n=∑' k : ℤ, a.val (n-k)*b.val k) ∧
        ‖c‖ ≤ C*‖a‖*‖b‖ := by
  have hr : 0 ≤ -s := neg_nonneg.mpr hs0
  have hgain : 1 < ((t+2)-(-s))*(2:ℝ≥0∞).toReal := by
    norm_num only [ENNReal.toReal_ofNat]
    linarith
  let B := sobolevHolderInclusion (p := 2) (r := 2) (q := 1)
    (t+2) (-s) (by norm_num) hgain
  have hw : SpectralWeight.one.negativeSobolev (-s)=Weight.sobolev s := by
    apply weight_eq_of_apply_eq
    intro k
    exact (SpectralWeight.one.negativeSobolev_eq_product (-s) k).trans
      (by simp only [neg_neg, SpectralWeight.one_apply, one_mul])
  refine ⟨‖B‖+1,by positivity,?_⟩
  rw [← hw]
  intro a b
  refine ⟨signedSobolevConvolution (-s) hr a (B b),?_,?_⟩
  · intro n
    have hsum := (evalCLM (SpectralWeight.one.negativeSobolev (-s)) ⊤ n).summable
      (summable_norm_signedSobolevConvolution_terms (-s) hr a (B b)).of_norm
    constructor
    · simpa only [map_smul, evalCLM_apply, SpectralWeight.negativeModulation_apply,
        smul_eq_mul, B, sobolevHolderInclusion_apply, mul_comm] using hsum
    · simpa only [B, sobolevHolderInclusion_apply] using
        signedSobolevConvolution_apply (-s) hr a (B b) n
  · calc
      _ ≤ ‖a‖*‖B b‖ := norm_signedSobolevConvolution_le (-s) hr a (B b)
      _ ≤ ‖a‖*(‖B‖*‖b‖) := mul_le_mul_of_nonneg_left (B.le_opNorm b) (norm_nonneg a)
      _ ≤ (‖B‖+1)*‖a‖*‖b‖ := by nlinarith [norm_nonneg a, norm_nonneg b]

end NLS.Articles.KdVPseudomeasures
