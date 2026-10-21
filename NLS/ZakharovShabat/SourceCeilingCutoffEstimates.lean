import NLS.ZakharovShabat.SourceFullCutoffEstimates

/-! # Sharper corrected Section 6 cutoff estimates

The original source norms and spectral data are retained. The additive leading-tail
term is not removed; the refuted printed estimates are not asserted.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Corrected original displacement budget with the source ceiling-half convention. -/
def sourcePeriodTwoDisplacementBudget_ceilingHalf (φ : CoeffPair p) (N : ℕ) : ℝ :=
  rootDisplacementSummationConstant p *
    (‖sourceFourierTail ((N+1)/2) φ‖^p.toReal +
      (‖φ‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖sourceFourierTail ((N+1)/2) φ‖^p.toReal) *
        (1+‖φ‖^p.toReal)*‖φ‖^p.toReal)

/-- Corrected weighted gap budget with the source ceiling-half convention. -/
def rootGapBudget_ceilingHalf (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) : ℝ :=
  rootGapSummationConstant p *
    (‖weightedPairFourierTail w.toWeight ((N+1)/2) φ‖^p.toReal +
      offDiagonalSummationConstant p * ‖φ‖^p.toReal *
        (‖φ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) +
          ‖weightedPairFourierTail w.toWeight ((N+1)/2) φ‖^(2*p.toReal)))

/-- The full-cutoff bound is at least as strong as the corrected ceiling-half bound. -/
theorem sourcePeriodTwoDisplacementBudget_fullCutoff_le_ceilingHalf
    (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) :
    sourcePeriodTwoDisplacementBudget_fullCutoff φ N ≤
      sourcePeriodTwoDisplacementBudget_ceilingHalf φ N := by
  have ht := norm_sourceFourierTail_antitone hp φ (show (N+1)/2 ≤ N by omega)
  have hc := rootDisplacementSummationConstant_nonneg p
  unfold sourcePeriodTwoDisplacementBudget_fullCutoff sourcePeriodTwoDisplacementBudget_ceilingHalf
  gcongr

/-- The same monotonicity applies to the weighted gap budget, with unchanged constants. -/
theorem rootGapBudget_fullCutoff_le_ceilingHalf
    (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) :
    rootGapBudget_fullCutoff w φ N ≤ rootGapBudget_ceilingHalf w φ N := by
  have ht := norm_weightedPairFourierTail_antitone hp w.toWeight φ
    (show (N+1)/2 ≤ N by omega)
  have hc := rootGapSummationConstant_nonneg p
  have he := offDiagonalSummationConstant_nonneg p
  unfold rootGapBudget_fullCutoff rootGapBudget_ceilingHalf
  gcongr

/-- The corrected source theorem retains its exact data and the ceiling-half Fourier tail. -/
theorem sourceProposition6_1_corrected_ceilingHalf (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs →
            PeriodicResonantPair hp SpectralWeight.one (unitWeightedPairEquiv ψ) n (ξ n) (η n)) ∧
          (∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z ∈ resonantStrip n,
            z ∉ sourceResolventSet hp ψ ↔ z = ξ n ∨ z = η n) ∧
          ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ sourcePeriodTwoDisplacementBudget_ceilingHalf ψ N := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := exists_uniform_sourcePeriodTwoDisplacement_fullCutoff hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hpair,hspec,ht⟩ := hr ψ hψ
  refine ⟨ξ,η,hpair,hspec,?_⟩
  intro K hK
  exact ⟨(ht K hK).1,(ht K hK).2.trans (sourcePeriodTwoDisplacementBudget_fullCutoff_le_ceilingHalf hp ψ K)⟩

/-- The corrected source theorem retains its exact data and the ceiling-half Fourier tail. -/
theorem sourceProposition6_3_corrected_ceilingHalf (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs → PeriodicResonantPair hp w ψ n (ξ n) (η n)) ∧
          (∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z ∈ resonantStrip n,
            z ∉ sourceResolventSet hp (sourceWeightedPeriodTwoInput w ψ) ↔ z = ξ n ∨ z = η n) ∧
          ∀ N : ℕ, N₀ ≤ N →
            Summable (periodicGapPowerTail hp w ψ N) ∧
            (∑' n : ℤ, periodicGapPowerTail hp w ψ N n) ≤ rootGapBudget_ceilingHalf w ψ N := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := sourceProposition6_3_corrected_fullCutoff hp hp1 w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hpair,hspec,ht⟩ := hr ψ hψ
  refine ⟨ξ,η,hpair,hspec,?_⟩
  intro K hK
  exact ⟨(ht K hK).1,(ht K hK).2.trans (rootGapBudget_fullCutoff_le_ceilingHalf hp w ψ K)⟩

/-- The corrected source theorem retains its exact data and the ceiling-half Fourier tail. -/
theorem sourceLemma6_9_ceilingHalf (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ n : ℤ, N₀ ≤ n.natAbs →
        AnalyticOnNhd ℂ (fun s : CoeffPair p × ℂ => sourceResonantDeterminantFunction hp s.1 n s.2)
          (U ×ˢ resonantStrip n) ∧ ∀ ψ ∈ U, SourceResonantStripControl hp ψ n) ∧
      ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ,
        (∀ n : ℤ, N₀ ≤ n.natAbs → SourceResonantRootPair hp ψ n (ξ n) (η n)) ∧
        ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail p N ξ η) ∧
          (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ sourcePeriodTwoDisplacementBudget_ceilingHalf ψ N := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hcontrol,hr⟩ := sourceLemma6_9_fullCutoff hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,hcontrol,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hpair,ht⟩ := hr ψ hψ
  refine ⟨ξ,η,hpair,?_⟩
  intro K hK
  exact ⟨(ht K hK).1,(ht K hK).2.trans
    (sourcePeriodTwoDisplacementBudget_fullCutoff_le_ceilingHalf hp ψ K)⟩

end NLS.ZakharovShabat
