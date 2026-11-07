import NLS.KdV.HillWienerNormalizedTail
import NLS.SequenceSpaces.WeightedConvolutionRowBound

/-! Positive ell-one domination of every actual normalized Hill tail
operator, uniformly in its mode, its spectral parameter and its forcing sign. -/
noncomputable section
open scoped ENNReal
open NLS.WeightedCoeff
namespace NLS.KdV

def hillWienerMagnitude (w : SpectralWeight) (q : WeightedCoeff (w.negativeSobolev 0) 1) : Coeff 1 :=
  Coeff.magnitude (weightEquiv (w.negativeSobolev 0) 1 q)

theorem norm_hillWienerMagnitude (w : SpectralWeight) (q : WeightedCoeff (w.negativeSobolev 0) 1) :
    ‖hillWienerMagnitude w q‖ = ‖q‖ := Coeff.norm_magnitude _

theorem norm_hillWienerMagnitude_apply (w : SpectralWeight)
    (q : WeightedCoeff (w.negativeSobolev 0) 1) (k : ℤ) :
    ‖hillWienerMagnitude w q k‖ = w k*‖q.val k‖ := by
  change ‖(‖(weightEquiv (w.negativeSobolev 0) 1 q) k‖:ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), weightEquiv_apply, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg ((w.negativeSobolev 0).positive k).le]
  simp only [SpectralWeight.negativeSobolev_apply, Weight.sobolev_zero_apply, div_one]

private theorem young_one_top_top : YoungRelation 1 ⊤ ⊤ := by norm_num [YoungRelation]

theorem hillWienerNormalizedTail_row_bound (w : SpectralWeight)
    (q : WeightedCoeff (w.negativeSobolev 0) 1) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (j : ℤ) (f : Coeff ⊤) (δ : ℝ)
    (hsymbol : ∀ k, ‖reducedHillSymbol n hn z hz k‖ ≤ δ) (m : ℤ) :
    ‖hillWienerNormalizedTail w n hn z hz (exponentInclusion _ (show 1 ≤ (⊤:ℝ≥0∞) from le_top) q) j f m‖ ≤
      δ*(∑' k : ℤ, ‖hillWienerMagnitude w q (m-k)‖*‖f k‖) := by
  let F := fun k : ℤ => (w m:ℂ)*q.val (m-k)*reducedHillSymbol n hn z hz (k+j)*f k/(w k:ℂ)
  have hb (k : ℤ) : ‖F k‖ ≤ δ*(‖hillWienerMagnitude w q (m-k)‖*‖f k‖) := by
    rw [norm_hillWienerMagnitude_apply]
    have hw : w m ≤ w (m-k)*w k := by simpa only [sub_add_cancel] using w.add_le (m-k) k
    exact (norm_weighted_convolution_term_le (w m) (w k) (w (m-k)) (w.positive _).le
      (w.positive _) (w.positive _).le hw (q.val (m-k)) (reducedHillSymbol n hn z hz (k+j))
        (f k) δ (hsymbol (k+j))).trans_eq (mul_assoc _ _ _)
  have hs : Summable (fun k : ℤ => ‖hillWienerMagnitude w q (m-k)‖*‖f k‖) := by
    simpa only [norm_mul] using Coeff.summable_norm_youngConvolution_terms young_one_top_top
      (hillWienerMagnitude w q) f m
  have hF := (hs.mul_left δ).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  rw [hillWienerNormalizedTail_apply]
  simp only [exponentInclusion_apply]
  exact (norm_tsum_le_tsum_norm hF).trans
    (by simpa only [tsum_mul_left] using hF.tsum_le_tsum hb (hs.mul_left δ))

theorem hillWienerNormalizedTail_positive_domination (w : SpectralWeight)
    (q : WeightedCoeff (w.negativeSobolev 0) 1) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (j : ℤ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsymbol : ∀ k, ‖reducedHillSymbol n hn z hz k‖ ≤ δ)
    (f : Coeff ⊤) (v : Coeff 1) (hv : Coeff.IsNonnegative v)
    (hfv : ∀ k, ‖f k‖ ≤ ‖v k‖) (m : ℤ) :
    ‖hillWienerNormalizedTail w n hn z hz (exponentInclusion _ (show 1 ≤ (⊤:ℝ≥0∞) from le_top) q) j f m‖ ≤
      ‖Coeff.positiveConvolutionOperator (hillWienerMagnitude w q) δ v m‖ := by
  have ha : Coeff.IsNonnegative (hillWienerMagnitude w q) := Coeff.isNonnegative_magnitude _
  have he := Coeff.norm_positiveConvolutionOperator_apply_of_nonnegative
    (hillWienerMagnitude w q) ha δ hδ v hv m
  apply (hillWienerNormalizedTail_row_bound w q n hn z hz j f δ hsymbol m).trans
  apply le_trans _ he.symm.le
  apply mul_le_mul_of_nonneg_left _ hδ
  have hs (b : Coeff 1) : Summable (fun k : ℤ => ‖hillWienerMagnitude w q (m-k)‖*‖b k‖) := by
    simpa only [norm_mul] using Coeff.summable_norm_youngConvolution_terms
      (show YoungRelation 1 1 1 by norm_num [YoungRelation]) (hillWienerMagnitude w q) b m
  have hsf : Summable (fun k : ℤ => ‖hillWienerMagnitude w q (m-k)‖*‖f k‖) := by
    simpa only [norm_mul] using Coeff.summable_norm_youngConvolution_terms young_one_top_top
      (hillWienerMagnitude w q) f m
  exact hsf.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hfv k) (norm_nonneg _)) (hs v)

end NLS.KdV
