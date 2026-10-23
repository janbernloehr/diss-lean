import NLS.ZakharovShabat.SourcePeriodTwoCompleteLabels
import NLS.ZakharovShabat.OrderedPeriodicUniqueness

/-! # Ordered complete spectra for arbitrary period-two input

The actual central enumeration and the distant pairs can be sorted without
an even-support hypothesis. The symmetric displacement tail is unchanged
past the central cutoff, so both the corrected estimate and local smallness
apply to these globally ordered labels.
-/
noncomputable section
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Permuting the two roots at each high index preserves the symmetric power tail. -/
theorem rootDisplacementPowerTail_eq_of_high_pair_multiset (p : ℝ≥0∞) (K : ℕ)
    (α β ξ η : ℤ → ℂ)
    (h : ∀ n : ℤ, K ≤ n.natAbs → ({α n,β n} : Multiset ℂ) = {ξ n,η n}) :
    rootDisplacementPowerTail p K α β = rootDisplacementPowerTail p K ξ η := by
  funext n
  unfold rootDisplacementPowerTail
  split_ifs with hn
  · have hs := congrArg (fun s : Multiset ℂ =>
        (s.map (fun z => ‖z-(Real.pi : ℂ)*n‖^p.toReal)).sum) (h n hn)
    simpa using hs
  · rfl

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Complete original period-two spectra admit globally ordered labels at every later cutoff. -/
theorem sourceProposition6_1_ordered_labels (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∀ N : ℕ, N₀ ≤ N → ∃ ξ η : ℤ → ℂ,
          PeriodicEndpointLabeling hp (CoeffPair.toMax p ψ) N ξ η ∧
          (∀ n, complexLexLE (ξ n) (η n)) ∧
          ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j) := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := sourceProposition6_1_complete_labels hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ K hK
  obtain ⟨ξ,η,h⟩ := hr ψ hψ K hK
  obtain ⟨α,β,hab,hw,ho,_⟩ := h.exists_ordered
  exact ⟨α,β,hab,hw,ho⟩

/-- The complete ordered source spectrum retains the corrected budget and locally small tails. -/
theorem sourceProposition6_1_ordered_asymptotics (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          PeriodicEndpointLabeling hp (CoeffPair.toMax p ψ) N₀ ξ η ∧
          (∀ n, complexLexLE (ξ n) (η n)) ∧
          (∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j)) ∧
          ∀ K : ℕ, N₀ < K → Summable (rootDisplacementPowerTail p K ξ η) ∧
            (∑' n : ℤ, rootDisplacementPowerTail p K ξ η n) ≤ sourcePeriodTwoDisplacementBudget ψ K ∧
            (∑' n : ℤ, rootDisplacementPowerTail p K ξ η n) < ε := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := sourceProposition6_1_complete_asymptotics hp hp1 φ hε
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hlabel,ht⟩ := hr ψ hψ
  obtain ⟨α,β,hab,hw,ho,hpair⟩ := hlabel.exists_ordered
  refine ⟨α,β,hab,hw,ho,?_⟩
  intro K hK
  rw [rootDisplacementPowerTail_eq_of_high_pair_multiset p K α β ξ η
    (fun n hn => hpair n (by omega))]
  exact ht K hK

end NLS.ZakharovShabat
