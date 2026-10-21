import NLS.ZakharovShabat.FullCutoffSpectralRoots
import NLS.ZakharovShabat.SourceLemma6_9
import NLS.ZakharovShabat.SourceWeightedGapAsymptotics

/-! # Sharper corrected Section 6 cutoff estimates

The original source norms and spectral data are retained. The additive leading-tail
term is not removed; the refuted printed estimates are not asserted.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original source estimate uses the full Fourier cutoff in its corrected budget. -/
def sourcePeriodTwoDisplacementBudget_fullCutoff (φ : CoeffPair p) (N : ℕ) : ℝ :=
  rootDisplacementSummationConstant p *
    (‖sourceFourierTail N φ‖^p.toReal +
      (‖φ‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖sourceFourierTail N φ‖^p.toReal) *
        (1+‖φ‖^p.toReal)*‖φ‖^p.toReal)

/-- The original source estimate uses the full Fourier cutoff in its corrected budget. -/
theorem rootDisplacementBudget_unitWeightedPairEquiv_fullCutoff (φ : CoeffPair p) (N : ℕ) :
    rootDisplacementBudget_fullCutoff SpectralWeight.one (unitWeightedPairEquiv φ) N =
      sourcePeriodTwoDisplacementBudget_fullCutoff φ N := by
  simp only [rootDisplacementBudget_fullCutoff, sourcePeriodTwoDisplacementBudget_fullCutoff,
    weightedPairFourierTail_unitWeightedPairEquiv, LinearIsometryEquiv.norm_map]

/-- The original source estimate uses the full Fourier cutoff in its corrected budget. -/
theorem sourcePeriodTwoDisplacementData_fullCutoff (hp : p ≠ ⊤) (ψ : CoeffPair p) (N : ℕ)
    (ξ η : ℤ → ℂ)
    (hr : ∀ n : ℤ, N ≤ n.natAbs →
      PeriodicResonantPair hp SpectralWeight.one (unitWeightedPairEquiv ψ) n (ξ n) (η n))
    (ht : ∀ K : ℕ, N ≤ K → Summable (rootDisplacementPowerTail p K ξ η) ∧
      (∑' n : ℤ, rootDisplacementPowerTail p K ξ η n) ≤
        rootDisplacementBudget_fullCutoff SpectralWeight.one (unitWeightedPairEquiv ψ) K) :
    (∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
      z ∉ sourceResolventSet hp ψ ↔ z = ξ n ∨ z = η n) ∧
    ∀ K : ℕ, N ≤ K → Summable (rootDisplacementPowerTail p K ξ η) ∧
      (∑' n : ℤ, rootDisplacementPowerTail p K ξ η n) ≤ sourcePeriodTwoDisplacementBudget_fullCutoff ψ K := by
  constructor
  · intro n hn z hz
    exact (sourcePeriodTwoSpectrum_iff hp ψ z).trans ((hr n hn).spectrum_iff z hz)
  · intro K hK
    exact ⟨(ht K hK).1,(ht K hK).2.trans_eq (rootDisplacementBudget_unitWeightedPairEquiv_fullCutoff ψ K)⟩

/-- The original source estimate uses the full Fourier cutoff in its corrected budget. -/
theorem exists_uniform_sourcePeriodTwoDisplacement_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs →
            PeriodicResonantPair hp SpectralWeight.one (unitWeightedPairEquiv ψ) n (ξ n) (η n)) ∧
          (∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z ∈ resonantStrip n,
            z ∉ sourceResolventSet hp ψ ↔ z = ξ n ∨ z = η n) ∧
          ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ sourcePeriodTwoDisplacementBudget_fullCutoff ψ N := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hroots⟩ := sourceUnitWeightedUniformPullback
    unitWeightedPairEquiv φ _
    (exists_uniform_periodicRoots_with_power_sums_fullCutoff hp hp1 SpectralWeight.one (unitWeightedPairEquiv φ))
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hr,ht⟩ := hroots ψ hψ
  obtain ⟨hs,hb⟩ := sourcePeriodTwoDisplacementData_fullCutoff hp ψ N ξ η hr
    (fun K hK => ⟨(ht K hK).1,(ht K hK).2.1⟩)
  exact ⟨ξ,η,hr,hs,hb⟩

/-- The original source estimate uses the full Fourier cutoff in its corrected budget. -/
theorem sourceProposition6_3_corrected_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs → PeriodicResonantPair hp w ψ n (ξ n) (η n)) ∧
          (∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z ∈ resonantStrip n,
            z ∉ sourceResolventSet hp (sourceWeightedPeriodTwoInput w ψ) ↔ z = ξ n ∨ z = η n) ∧
          ∀ N : ℕ, N₀ ≤ N →
            Summable (periodicGapPowerTail hp w ψ N) ∧
            (∑' n : ℤ, periodicGapPowerTail hp w ψ N n) ≤ rootGapBudget_fullCutoff w ψ N := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := exists_uniform_periodicRoots_with_power_sums_fullCutoff hp hp1 w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hpair,ht⟩ := hr ψ hψ
  refine ⟨ξ,η,hpair,?_,?_⟩
  · intro n hn z hz
    exact (sourceWeightedPeriodTwoSpectrum_iff hp w ψ z).trans ((hpair n hn).spectrum_iff z hz)
  · intro K hK
    rw [periodicGapPowerTail_eq_rootGapPowerTail hp w ψ K ξ η
      (fun n hn => (hpair n (hK.trans hn)).squaredGap_eq)]
    exact (ht K hK).2.2

/-- The original source estimate uses the full Fourier cutoff in its corrected budget. -/
theorem sourceLemma6_9_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ n : ℤ, N₀ ≤ n.natAbs →
        AnalyticOnNhd ℂ (fun s : CoeffPair p × ℂ => sourceResonantDeterminantFunction hp s.1 n s.2)
          (U ×ˢ resonantStrip n) ∧ ∀ ψ ∈ U, SourceResonantStripControl hp ψ n) ∧
      ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ,
        (∀ n : ℤ, N₀ ≤ n.natAbs → SourceResonantRootPair hp ψ n (ξ n) (η n)) ∧
        ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail p N ξ η) ∧
          (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ sourcePeriodTwoDisplacementBudget_fullCutoff ψ N := by
  obtain ⟨Nc,hNc,V,hoV,hcV,hφV,h0V,hcontrol⟩ := exists_uniform_sourceResonantDeterminant_control hp hp1 φ
  obtain ⟨Nr,_,W,hoW,hcW,hφW,h0W,hroots⟩ := exists_uniform_sourcePeriodTwoDisplacement_fullCutoff hp hp1 φ
  refine ⟨max Nc Nr,hNc.trans (le_max_left _ _),V ∩ W,hoV.inter hoW,hcV.inter hcW,
    ⟨hφV,hφW⟩,⟨h0V,h0W⟩,?_,?_⟩
  · intro n hn
    refine ⟨?_,fun ψ hψ => (hcontrol n (by omega)).2 ψ hψ.1⟩
    intro s hs
    exact (hcontrol n (by omega)).1 s ⟨hs.1.1,hs.2⟩
  · intro ψ hψ
    obtain ⟨ξ,η,hr,_,ht⟩ := hroots ψ hψ.2
    exact ⟨ξ,η,fun n hn => SourceResonantRootPair.of_periodic (hr n (by omega)) ((hcontrol n (by omega)).2 ψ hψ.1),
      fun N hN => ht N (by omega)⟩

end NLS.ZakharovShabat
