import NLS.ZakharovShabat.SourceCoefficientFullCutoffs
import NLS.ZakharovShabat.WeightedContraction

/-! # Sharper corrected Section 6 cutoff estimates

The original source norms and spectral data are retained. The additive leading-tail
term is not removed; the refuted printed estimates are not asserted.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original coefficient budget with the ceiling-half Fourier tail. -/
def sourceDiagonalTailBudget_ceilingHalf (φ : CoeffPair p) (N : ℕ) : ℝ :=
  diagonalSummationConstant p * ‖φ‖^p.toReal *
    (‖φ‖^p.toReal / (N : ℝ)^(min 1 (p.toReal-1)) + ‖sourceFourierTail ((N+1)/2) φ‖^p.toReal)

/-- Original coefficient budget with the ceiling-half Fourier tail. -/
def sourceOffDiagonalTailBudget_ceilingHalf (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    (componentNorm : ℝ) (N : ℕ) : ℝ :=
  offDiagonalSummationConstant p * componentNorm^p.toReal *
    (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
      ‖weightedPairFourierTail w.toWeight ((N+1)/2) φ‖^(2*p.toReal))

/-- Original coefficient budget with the ceiling-half Fourier tail. -/
def SourceCoefficientTailEstimates_ceilingHalf (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) : Prop :=
  let ψ := sourceWeightedPeriodTwoInput w φ
  (Summable (sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp ψ)) ∧
    (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp ψ) n) ≤ sourceDiagonalTailBudget_ceilingHalf ψ N) ∧
  (Summable (sourceCoefficientPowerTail p N (sourceResonantBMinusSup hp w ψ)) ∧
    (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantBMinusSup hp w ψ) n) ≤ sourceOffDiagonalTailBudget_ceilingHalf w φ ‖φ.fst‖ N) ∧
  (Summable (sourceCoefficientPowerTail p N (sourceResonantBPlusSup hp w ψ)) ∧
    (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantBPlusSup hp w ψ) n) ≤ sourceOffDiagonalTailBudget_ceilingHalf w φ ‖φ.snd‖ N)

/-- Monotonicity passes the stronger original diagonal bound to the ceiling-half cutoff. -/
theorem sourceDiagonalTailBudget_fullCutoff_le_ceilingHalf
    (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) :
    sourceDiagonalTailBudget_fullCutoff φ N ≤ sourceDiagonalTailBudget_ceilingHalf φ N := by
  have ht := norm_sourceFourierTail_antitone hp φ (show (N+1)/2 ≤ N by omega)
  have hc := diagonalSummationConstant_nonneg (p := p)
  unfold sourceDiagonalTailBudget_fullCutoff sourceDiagonalTailBudget_ceilingHalf
  gcongr

/-- The weighted off-diagonal comparison preserves the distinguished component factor. -/
theorem sourceOffDiagonalTailBudget_fullCutoff_le_ceilingHalf
    (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    (c : ℝ) (hc : 0 ≤ c) (N : ℕ) :
    sourceOffDiagonalTailBudget_fullCutoff w φ c N ≤
      sourceOffDiagonalTailBudget_ceilingHalf w φ c N := by
  have ht := norm_weightedPairFourierTail_antitone hp w.toWeight φ
    (show (N+1)/2 ≤ N by omega)
  have he := offDiagonalSummationConstant_nonneg p
  unfold sourceOffDiagonalTailBudget_fullCutoff sourceOffDiagonalTailBudget_ceilingHalf
  gcongr

/-- All three actual supremum tails retain their summability and ceiling-half budgets. -/
theorem SourceCoefficientTailEstimates_fullCutoff.to_ceilingHalf
    (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (N : ℕ)
    (h : SourceCoefficientTailEstimates_fullCutoff hp w φ N) :
    SourceCoefficientTailEstimates_ceilingHalf hp w φ N := by
  rcases h with ⟨ha,hm,hb⟩
  exact ⟨⟨ha.1,ha.2.trans (sourceDiagonalTailBudget_fullCutoff_le_ceilingHalf hp _ N)⟩,
    ⟨hm.1,hm.2.trans (sourceOffDiagonalTailBudget_fullCutoff_le_ceilingHalf hp w φ _ (norm_nonneg _) N)⟩,
    ⟨hb.1,hb.2.trans (sourceOffDiagonalTailBudget_fullCutoff_le_ceilingHalf hp w φ _ (norm_nonneg _) N)⟩⟩

/-- The source coefficient theorem holds with the ceiling-half tail and all original quantifiers. -/
theorem sourceLemma6_8_summability_ceilingHalf (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → SourceCoefficientTailEstimates_ceilingHalf hp w ψ N := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hs⟩ := sourceLemma6_8_summability_fullCutoff hp hp1 w φ
  exact ⟨N,hN,U,ho,hc,hφ,h0,fun ψ hψ K hK =>
    SourceCoefficientTailEstimates_fullCutoff.to_ceilingHalf hp w ψ K (hs ψ hψ K hK)⟩

/-- The source coefficient theorem holds with the ceiling-half tail and all original quantifiers. -/
theorem sourceLemma6_8_quantitative_ceilingHalf (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ∀ n : ℤ, N₀ ≤ n.natAbs → SourceCoefficientStripBounds hp w (sourceWeightedPeriodTwoInput w ψ) n) ∧
      (∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → SourceCoefficientTailEstimates_ceilingHalf hp w ψ N) := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hb,hs⟩ := sourceLemma6_8_quantitative_fullCutoff hp hp1 w φ
  exact ⟨N,hN,U,ho,hc,hφ,h0,hb,fun ψ hψ K hK =>
    SourceCoefficientTailEstimates_fullCutoff.to_ceilingHalf hp w ψ K (hs ψ hψ K hK)⟩

/-- The source coefficient theorem holds with the ceiling-half tail and all original quantifiers. -/
theorem sourceLemma6_8_unweighted_ceilingHalf (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U,
        (∀ n : ℤ, N₀ ≤ n.natAbs → SourceCoefficientStripBounds hp SpectralWeight.one ψ n) ∧
        (∀ N : ℕ, N₀ ≤ N → SourceCoefficientTailEstimates_ceilingHalf hp SpectralWeight.one (unitWeightedPairEquiv ψ) N) := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hs⟩ := sourceLemma6_8_unweighted_fullCutoff hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  exact ⟨(hs ψ hψ).1,fun K hK =>
    SourceCoefficientTailEstimates_fullCutoff.to_ceilingHalf hp SpectralWeight.one
      (unitWeightedPairEquiv ψ) K ((hs ψ hψ).2 K hK)⟩

end NLS.ZakharovShabat
