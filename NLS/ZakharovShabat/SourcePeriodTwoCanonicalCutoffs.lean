import NLS.ZakharovShabat.SourcePeriodTwoCanonicalEndpoints
import NLS.ZakharovShabat.SourceCeilingCutoffEstimates
import NLS.ZakharovShabat.SourcePositiveDisplacementTail

/-! # Stronger corrected cutoff bounds for fixed period-two eigenvalue labels

The complete canonical sequences inherit the full-cutoff displacement
estimate from equality of the actual high-pair multisets. The ceiling-half
budget and the literal positive-index range follow by domination.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The fixed complete canonical labels satisfy the stronger full-Fourier-cutoff estimate. -/
theorem sourceProposition6_1_canonical_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ K : ℕ, N₀ < K →
        Summable (rootDisplacementPowerTail p K (sourcePeriodTwoCanonicalLeft hp hp1 ψ)
          (sourcePeriodTwoCanonicalRight hp hp1 ψ)) ∧
        (∑' n : ℤ, rootDisplacementPowerTail p K (sourcePeriodTwoCanonicalLeft hp hp1 ψ)
          (sourcePeriodTwoCanonicalRight hp hp1 ψ) n) ≤ sourcePeriodTwoDisplacementBudget_fullCutoff ψ K := by
  obtain ⟨Nc,hNc,V,hoV,hcV,hφV,h0V,hcanon⟩ :=
    sourceProposition6_1_canonical_asymptotics hp hp1 φ (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Nr,_,W,hoW,hcW,hφW,h0W,hr⟩ := exists_uniform_sourcePeriodTwoDisplacement_fullCutoff hp hp1 φ
  refine ⟨max Nc Nr,hNc.trans (le_max_left _ _),V ∩ W,hoV.inter hoW,hcV.inter hcW,
    ⟨hφV,hφW⟩,⟨h0V,h0W⟩,?_⟩
  intro ψ hψ K hK
  obtain ⟨ξ,η,hpair,_,ht⟩ := hr ψ hψ.2
  have he (n : ℤ) (hn : K ≤ n.natAbs) :
      ({sourcePeriodTwoCanonicalLeft hp hp1 ψ n,sourcePeriodTwoCanonicalRight hp hp1 ψ n} : Multiset ℂ) =
        {ξ n,η n} := by
    have hpairs := (hpair n (by omega)).toEndpoints
    rw [weightedBaseToPair_unitWeightedPairEquiv] at hpairs
    exact ((hcanon ψ hψ.1).1.distant n (by omega)).multiset_eq hpairs
  rw [rootDisplacementPowerTail_eq_of_high_pair_multiset p K _ _ ξ η he]
  exact ht K (by omega)

/-- Both exact positive-index corrected budgets hold for the same fixed canonical labels. -/
theorem sourceProposition6_1_canonical_positive_cutoffs (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ K : ℕ, N₀ < K →
        Summable (sourcePositiveDisplacementPowerTail p K (sourcePeriodTwoCanonicalLeft hp hp1 ψ)
          (sourcePeriodTwoCanonicalRight hp hp1 ψ)) ∧
        (∑' n : ℤ, sourcePositiveDisplacementPowerTail p K (sourcePeriodTwoCanonicalLeft hp hp1 ψ)
          (sourcePeriodTwoCanonicalRight hp hp1 ψ) n) ≤ sourcePeriodTwoDisplacementBudget_fullCutoff ψ K ∧
        (∑' n : ℤ, sourcePositiveDisplacementPowerTail p K (sourcePeriodTwoCanonicalLeft hp hp1 ψ)
          (sourcePeriodTwoCanonicalRight hp hp1 ψ) n) ≤ sourcePeriodTwoDisplacementBudget_ceilingHalf ψ K := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,ht⟩ := sourceProposition6_1_canonical_fullCutoff hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ K hK
  obtain ⟨hs,hb⟩ := ht ψ hψ K hK
  have hb' := (tsum_sourcePositiveDisplacementPowerTail_le p K _ _ hs).trans hb
  exact ⟨summable_sourcePositiveDisplacementPowerTail p K _ _ hs,hb',
    hb'.trans (sourcePeriodTwoDisplacementBudget_fullCutoff_le_ceilingHalf hp ψ K)⟩

end NLS.ZakharovShabat
