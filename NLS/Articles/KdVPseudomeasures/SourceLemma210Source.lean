import NLS.Articles.KdVPseudomeasures.SourceLemma210Extended

/-! The source test domain in Lemma 2.10, with actual original Fourier
coefficients and no additional weighted membership hypothesis. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff NLS.ReciprocalSeries
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem source_resonant_series_summable_plus (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    Summable (fun k : ℤ => ‖q.val ((n:ℤ)-k)*wideHillSymbol n z k*f.val k‖) := by
  let W := w.negativeSobolev r (2*(n:ℤ))
  let M := ((2:ℝ)^(2*r)*(n:ℝ)^(-r))*‖q‖*w.negativeShiftedNorm r hr (n:ℤ) ⊤ f
  have hW : 0<W := (w.negativeSobolev r).positive _
  have hmajor := (quadraticPowerKernel_twoScale_bound (1-r) (by linarith) n (by omega)).1.mul_left M
  have hs := hmajor.of_nonneg_of_le (fun k => mul_nonneg hW.le (norm_nonneg
      (q.val ((n:ℤ)-k)*wideHillSymbol n z k*f.val k)))
      (source_resonant_term_bound w r hr n hn z hz q f)
  simpa only [← mul_assoc,inv_mul_cancel₀ hW.ne',one_mul] using hs.mul_left W⁻¹

theorem source_resonant_series_summable (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev r) ⊤) (l : ℤ)
    (hl : l=(n:ℤ) ∨ l=-(n:ℤ)) :
    Summable (fun k : ℤ => ‖q.val (l-k)*wideHillSymbol n z k*f.val k‖) := by
  rcases hl with rfl | rfl
  · exact source_resonant_series_summable_plus w r hr hr1 n hn z hz q f
  · have hs := (Equiv.neg ℤ).summable_iff.mpr (source_resonant_series_summable_plus w r hr hr1 n hn z hz
      (weightReflection _ (w.negativeSobolev_neg r) q)
      (weightReflection _ (w.negativeSobolev_neg r) f))
    have he (k : ℤ) : -((n:ℤ)- -k)=-(n:ℤ)-k := by omega
    simpa only [Function.comp_def,Equiv.neg_apply,weightReflection_apply,neg_neg,wideHillSymbol,
      Int.natAbs_neg,freeHillValue_neg,he] using hs

/-- Lemma 2.10 for every original unweighted endpoint distribution f.
The undefined printed exponent p is infinity. The extended supremum makes
sense even if f has infinite norm in the extra spectral weight. -/
theorem sourceLemma2_10_original (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) :
    ∃ C : ℝ, 1≤C ∧ 13*endpointHillConstant r≤C ∧
      ∀ (w : SpectralWeight)
      (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
      (f : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
      (n : ℕ) (_hn : 2≤n) (z : ℂ) (_hz : z ∈ wideHillStrip n)
      (l : ℤ), (l=(n:ℤ) ∨ l=-(n:ℤ)) →
        Summable (fun k : ℤ => ‖q.val (mode (-(l-k)))*wideHillSymbol n z k*f.val (mode (-k))‖) ∧
        ENNReal.ofReal (w.negativeSobolev r (2*(n:ℤ))*
          ‖∑' k : ℤ, q.val (mode (-(l-k)))*wideHillSymbol n z k*f.val (mode (-k))‖) ≤
          ENNReal.ofReal (C*sourcePredualEpsilon r n*‖q‖)*
            sourceShiftedENorm (w.negativeSobolev r) l (fun k => f.val (mode (-k))) := by
  obtain ⟨C,hC,hCwide,h⟩ := sourceLemma2_10_extended r hr hr1
  refine ⟨C,hC,hCwide,?_⟩
  intro w q f n hn z hz l hl
  constructor
  · simpa only [endpointForgetWeight_apply,sourceWeightedEndpointCoefficients_apply,
      sourceEndpointCoefficients_apply] using source_resonant_series_summable SpectralWeight.one r hr hr1 n hn z hz
      (endpointForgetWeight w r (sourceWeightedEndpointCoefficients w r q))
      (sourceEndpointCoefficients r f) l hl
  · simpa only [sourceWeightedEndpointCoefficients_apply,norm_sourceWeightedEndpointCoefficients] using
      h w (sourceWeightedEndpointCoefficients w r q) (fun k => f.val (mode (-k))) n hn z hz l hl

end NLS.Articles.KdVPseudomeasures
