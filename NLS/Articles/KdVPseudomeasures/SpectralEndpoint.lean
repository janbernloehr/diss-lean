import NLS.KdV.PseudomeasureTailInverse

/-!
# The article's shifted-infinity Hill bounds

These are the literal Fourier-coefficient operator estimates in Lemma 2.4
and the contraction/invertibility consequences of Corollary 2.5. The full
range -1/2<s<=0 and arbitrary source spectral weight are retained.

Correction: the strip radius is 6*n, as in the shared verified free Hill
foundation. This replaces the printed radius 12*n; all eventual spectral
arguments must establish their eigenvalue inclusion in this corrected strip.
Physical singular-potential multiplication and the spectral eigenvalue
identification remain separate obligations, not hypotheses hidden here.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- Explicit source-order constant, independent of w, q and lambda. -/
def spectralEndpointConstant (s : ℝ) : ℝ := NLS.KdV.endpointHillConstant (-s)

/-- Exact identification with the source's weight w(k)<k>^s. -/
theorem source_negativeWeight_apply (w : SpectralWeight) (s : ℝ) (k : ℤ) :
    w.negativeSobolev (-s) k = w k * Weight.sobolev s k := by
  simpa only [neg_neg] using w.negativeSobolev_eq_product (-s) k

/-- The constant is at least one over the entire source regularity range. -/
theorem spectralEndpointConstant_one_le (s : ℝ) (hs : -(1:ℝ)/2<s) :
    1≤spectralEndpointConstant s := by
  unfold spectralEndpointConstant NLS.KdV.endpointHillConstant
  have hd : 0<1-2*(-s) := by linarith
  have hq : 0≤16/(1-2*(-s)) := div_nonneg (by norm_num) hd.le
  linarith

/-- The source constant decreases monotonically with increasing regularity s. -/
theorem spectralEndpointConstant_antitone :
    AntitoneOn spectralEndpointConstant (Ioc (-(1:ℝ)/2) 0) := by
  intro s hs t ht hst
  exact NLS.KdV.endpointHillConstant_mono (neg_le_neg hst) (by have hh:=hs.1; linarith)

/-- Lemma 2.4, both shifted operator norms, on the corrected spectral strip.
The named operators are constructed from absolutely convergent Fourier rows. -/
theorem sourceLemma2_4_coefficient_bounds (w : SpectralWeight)
    (s : ℝ) (hs : -(1:ℝ)/2<s) (hs0 : s≤0)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ NLS.KdV.reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev (-s)) ⊤) :
    ‖NLS.KdV.endpointHillPerturbation w (-s) (by linarith) (by linarith) n hn z hz q‖ ≤
      spectralEndpointConstant s * (n:ℝ)^(-(1/2-|s|)) * ‖q‖ ∧
    ‖NLS.KdV.endpointHillPerturbationMinus w (-s) (by linarith) (by linarith) n hn z hz q‖ ≤
      spectralEndpointConstant s * (n:ℝ)^(-(1/2-|s|)) * ‖q‖ := by
  have he : -s-1/2 = -(1/2-|s|) := by rw [abs_of_nonpos hs0]; ring
  constructor
  · simpa only [spectralEndpointConstant, he] using
      NLS.KdV.norm_endpointHillPerturbation_operator_le w (-s) (by linarith) (by linarith) n hn z hz q
  · simpa only [spectralEndpointConstant, he] using
      NLS.KdV.norm_endpointHillPerturbationMinus_operator_le w (-s) (by linarith) (by linarith) n hn z hz q

/-- Corollary 2.5: the cutoff precedes the weight, potential, mode and lambda,
so it works uniformly on norm-bounded sets and over the whole weight class. -/
theorem sourceCorollary2_5_coefficient_tail_invertible
    (s : ℝ) (hs : -(1:ℝ)/2<s) (hs0 : s≤0) (R : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ (w : SpectralWeight)
      (q : WeightedCoeff (w.negativeSobolev (-s)) ⊤), ‖q‖≤R →
      ∀ (n : ℕ) (hn : 1≤n), N≤n → ∀ (z : ℂ) (hz : z ∈ NLS.KdV.reducedHillStrip n),
        IsUnit (1-NLS.KdV.endpointHillPerturbation w (-s) (by linarith) (by linarith) n hn z hz q) ∧
        IsUnit (1-NLS.KdV.endpointHillPerturbationMinus w (-s) (by linarith) (by linarith) n hn z hz q) :=
  NLS.KdV.exists_endpointHill_uniform_tail_isUnit (-s) (by linarith) (by linarith) R

/-- Lemma 2.4 in the source's literal formulation: one operator on the
unshifted w<s>-weighted infinity space, estimated in both shifted norms. -/
theorem sourceLemma2_4_shiftedNorm_bounds (w : SpectralWeight)
    (s : ℝ) (hs : -(1:ℝ)/2<s) (hs0 : s≤0)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ NLS.KdV.reducedHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev (-s)) ⊤) :
    w.negativeShiftedNorm (-s) (by linarith) (n:ℤ) ⊤
      (NLS.KdV.unshiftedEndpointHillPerturbation w (-s) (by linarith) (by linarith) n hn z hz q f) ≤
        spectralEndpointConstant s*(n:ℝ)^(-(1/2-|s|))*‖q‖ *
          w.negativeShiftedNorm (-s) (by linarith) (n:ℤ) ⊤ f ∧
    w.negativeShiftedNorm (-s) (by linarith) (-(n:ℤ)) ⊤
      (NLS.KdV.unshiftedEndpointHillPerturbation w (-s) (by linarith) (by linarith) n hn z hz q f) ≤
        spectralEndpointConstant s*(n:ℝ)^(-(1/2-|s|))*‖q‖ *
          w.negativeShiftedNorm (-s) (by linarith) (-(n:ℤ)) ⊤ f := by
  have he : -s-1/2 = -(1/2-|s|) := by rw [abs_of_nonpos hs0]; ring
  simpa only [spectralEndpointConstant, he] using
    NLS.KdV.negativeShiftedNorm_endpointHillPerturbation_le w (-s) (by linarith) (by linarith)
      n hn z hz q f

end NLS.Articles.KdVPseudomeasures
