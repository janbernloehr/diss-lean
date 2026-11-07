import NLS.Articles.KdVPseudomeasures.SourcePrintedStripCounterexample
import NLS.Articles.KdVPseudomeasures.SpectralEndpoint
import NLS.KdV.PseudomeasureWideTail

/-! The full printed radius-12n strip is available at every n≥2.
Corollary 2.5 chooses its uniform cutoff at least two and therefore needs
no change of strip. The exceptional n=1 claim in Lemma 2.4 remains false. -/
noncomputable section
open Set NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def sourceWideEndpointConstant (s : ℝ) : ℝ := 13*spectralEndpointConstant s

theorem sourceWideEndpointConstant_one_le (s : ℝ) (hs : -(1:ℝ)/2<s) :
    1 ≤ sourceWideEndpointConstant s := by
  have h := spectralEndpointConstant_one_le s hs
  unfold sourceWideEndpointConstant
  linarith

theorem sourceWideEndpointConstant_antitone :
    AntitoneOn sourceWideEndpointConstant (Ioc (-(1:ℝ)/2) 0) := by
  intro s hs t ht hst
  exact mul_le_mul_of_nonneg_left (spectralEndpointConstant_antitone hs ht hst) (by norm_num)

/-- The printed Lemma 2.4 norm estimate for every valid wide-strip index.
Both shifted norms refer to the same actual Fourier convolution operator. -/
theorem sourceLemma2_4_wide (s : ℝ) (hs : -(1:ℝ)/2<s) (hs0 : s≤0)
    (w : SpectralWeight) (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ printedHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev (-s)) ⊤) :
    w.negativeShiftedNorm (-s) (by linarith) (n:ℤ) ⊤
      (wideEndpointHillPerturbation w (-s) (by linarith) (by linarith) n hn z hz q f) ≤
        sourceWideEndpointConstant s*(n:ℝ)^(-s-1/2)*‖q‖*
          w.negativeShiftedNorm (-s) (by linarith) (n:ℤ) ⊤ f ∧
    w.negativeShiftedNorm (-s) (by linarith) (-(n:ℤ)) ⊤
      (wideEndpointHillPerturbation w (-s) (by linarith) (by linarith) n hn z hz q f) ≤
        sourceWideEndpointConstant s*(n:ℝ)^(-s-1/2)*‖q‖*
          w.negativeShiftedNorm (-s) (by linarith) (-(n:ℤ)) ⊤ f :=
  negativeShiftedNorm_wideEndpointHillPerturbation_le w (-s) (by linarith) (by linarith) n hn z hz q f

/-- Corollary 2.5 on the entire printed strip. One cutoff precedes every
weight, potential in the norm ball and spectral parameter. The same
two-sided inverse has norm at most two in both shifted source norms. -/
theorem sourceCorollary2_5_wide (s : ℝ) (hs : -(1:ℝ)/2<s) (hs0 : s≤0) (R : ℝ) :
    ∃ N : ℕ, 2≤N ∧ ∀ (w : SpectralWeight)
      (q : WeightedCoeff (w.negativeSobolev (-s)) ⊤), ‖q‖≤R →
      ∀ (n : ℕ) (hn : 2≤n), N≤n → ∀ (z : ℂ) (hz : z ∈ printedHillStrip n),
        let T := wideEndpointHillPerturbation w (-s) (by linarith) (by linarith) n hn z hz q
        (∀ f,
          w.negativeShiftedNorm (-s) (by linarith) (n:ℤ) ⊤ (T f) ≤
            (1/2)*w.negativeShiftedNorm (-s) (by linarith) (n:ℤ) ⊤ f ∧
          w.negativeShiftedNorm (-s) (by linarith) (-(n:ℤ)) ⊤ (T f) ≤
            (1/2)*w.negativeShiftedNorm (-s) (by linarith) (-(n:ℤ)) ⊤ f) ∧
        ∃ K : WeightedCoeff (w.negativeSobolev (-s)) ⊤ →L[ℂ]
            WeightedCoeff (w.negativeSobolev (-s)) ⊤,
          (∀ f, K (f-T f)=f) ∧ (∀ f, K f-T (K f)=f) ∧
          ∀ f,
            w.negativeShiftedNorm (-s) (by linarith) (n:ℤ) ⊤ (K f) ≤
              2*w.negativeShiftedNorm (-s) (by linarith) (n:ℤ) ⊤ f ∧
            w.negativeShiftedNorm (-s) (by linarith) (-(n:ℤ)) ⊤ (K f) ≤
              2*w.negativeShiftedNorm (-s) (by linarith) (-(n:ℤ)) ⊤ f := by
  have hr : 0≤-s := by linarith
  have hr1 : -s<1/2 := by linarith
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff (-s) hr1 R
  refine ⟨N,hN,?_⟩
  intro w q hq n hn hNn z hz
  have hC : 0 ≤ 13*endpointHillConstant (-s)*(n:ℝ)^(-s-1/2) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (endpointHillConstant_pos (-s) hr1).le)
      (Real.rpow_nonneg (by positivity) _)
  have hsmall : 13*endpointHillConstant (-s)*(n:ℝ)^(-s-1/2)*‖q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq hC).trans (hcut n hNn)
  constructor
  · intro f
    have h := negativeShiftedNorm_wideEndpointHillPerturbation_le w (-s) hr hr1 n hn z hz q f
    exact ⟨h.1.trans (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)),
      h.2.trans (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _))⟩
  · exact ⟨wideEndpointHillTailInverse w (-s) hr hr1 n hn z hz q hsmall,
      wideEndpointHillTailInverse_left w (-s) hr hr1 n hn z hz q hsmall,
      wideEndpointHillTailInverse_right w (-s) hr hr1 n hn z hz q hsmall,
      negativeShiftedNorm_wideEndpointHillTailInverse_le w (-s) hr hr1 n hn z hz q hsmall⟩

end NLS.Articles.KdVPseudomeasures
