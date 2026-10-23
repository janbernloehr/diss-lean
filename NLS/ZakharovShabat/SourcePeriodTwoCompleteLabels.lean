import NLS.ZakharovShabat.PeriodicEndpointLabeling
import NLS.ZakharovShabat.SourcePeriodTwoAsymptotics

/-! # Complete periodic endpoint sequences for arbitrary period-two input

Actual central root multisets can be spliced into distant spectral pairs
without assuming even Fourier support. Every label is then an eigenvalue,
all spectral values are exhausted, and finite replacement preserves both
displacement classes. No parity or continuity of labels is asserted.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Finite splicing preserves the full actual central multiset, without parity assumptions. -/
theorem CentralPeriodicLabeling.splice {hp : p ≠ ⊤} {φ : PairSpace p}
    {N : ℕ} {α β : ℤ → ℂ} (h : CentralPeriodicLabeling hp φ N α β) (ξ η : ℤ → ℂ) :
    CentralPeriodicLabeling hp φ N (spliceCentralRoots N α ξ) (spliceCentralRoots N β η) := by
  constructor
  rw [← h.roots]
  apply Finset.sum_congr rfl
  intro n hn
  have hlow : ¬N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
  simp only [spliceCentralRoots, if_neg hlow]

/-- Any counted distant pairs can be completed using the actual central spectrum. -/
theorem exists_completePeriodicEndpointLabeling (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)) :
    ∃ α β : ℤ → ℂ, PeriodicEndpointLabeling hp (weightedBaseToPair w φ) N α β ∧
      ∀ n : ℤ, N < n.natAbs → α n = ξ n ∧ β n = η n := by
  obtain ⟨a,b,hab,_,_⟩ := exists_ordered_centralPeriodicLabeling hp _ N hc
  refine ⟨spliceCentralRoots N a ξ,spliceCentralRoots N b η,
    ⟨hc,hab.splice ξ η,?_,memℓp_spliceCentralRoots N a ξ hξ,
      memℓp_spliceCentralRoots N b η hη⟩,?_⟩
  · intro n hn
    simpa only [spliceCentralRoots,if_pos hn] using (hr n hn).toEndpoints
  · intro n hn
    simp only [spliceCentralRoots,if_pos hn,and_self]

/-- One neighborhood supplies complete endpoint sequences for every larger central cutoff. -/
theorem exists_uniform_completePeriodicEndpointLabeling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∀ N : ℕ, N₀ ≤ N → ∃ ξ η : ℤ → ℂ,
          PeriodicEndpointLabeling hp (weightedBaseToPair w ψ) N ξ η := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := exists_uniform_periodicSpectralProducts hp hp1 w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ K hK
  obtain ⟨ξ,η,hξ,hη,hpair,hd⟩ := hr ψ hψ
  obtain ⟨α,β,hab,_⟩ := exists_completePeriodicEndpointLabeling hp w ψ K (hd K hK).1 ξ η hξ hη
    (fun n hn => hpair n (by omega))
  exact ⟨α,β,hab⟩

/-- Original raw period-two input admits complete actual labels, including every central root. -/
theorem sourceProposition6_1_complete_labels (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∀ N : ℕ, N₀ ≤ N → ∃ ξ η : ℤ → ℂ,
          PeriodicEndpointLabeling hp (CoeffPair.toMax p ψ) N ξ η := by
  have h := sourceUnitWeightedUniformPullback unitWeightedPairEquiv φ _
    (exists_uniform_completePeriodicEndpointLabeling hp hp1 SpectralWeight.one (unitWeightedPairEquiv φ))
  simpa only [weightedBaseToPair_unitWeightedPairEquiv] using h

/-- Complete original labels exhaust the actual source-pencil spectrum. -/
theorem sourcePeriodTwo_complete_labels_exhaustive (hp : p ≠ ⊤) (φ : CoeffPair p)
    (N : ℕ) (ξ η : ℤ → ℂ) (h : PeriodicEndpointLabeling hp (CoeffPair.toMax p φ) N ξ η)
    (z : ℂ) : z ∉ sourceResolventSet hp φ ↔ ∃ n : ℤ, ξ n = z ∨ η n = z := by
  have hs := sourcePeriodTwoSpectrum_iff hp φ z
  rw [weightedBaseToPair_unitWeightedPairEquiv] at hs
  exact hs.trans (h.exhaustive z)

/-- Complete actual source labels retain the corrected bound and locally small high tails. -/
theorem sourceProposition6_1_complete_asymptotics (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          PeriodicEndpointLabeling hp (CoeffPair.toMax p ψ) N₀ ξ η ∧
          ∀ K : ℕ, N₀ < K → Summable (rootDisplacementPowerTail p K ξ η) ∧
            (∑' n : ℤ, rootDisplacementPowerTail p K ξ η n) ≤ sourcePeriodTwoDisplacementBudget ψ K ∧
            (∑' n : ℤ, rootDisplacementPowerTail p K ξ η n) < ε := by
  obtain ⟨Nr,hNr,V,hoV,hcV,hφV,h0V,hr⟩ := sourceProposition6_1_asymptotics hp hp1 φ hε
  obtain ⟨Nc,W,_,hoW,hcW,hφW,h0W,_,_,hcount⟩ :=
    exists_uniform_periodicCountingData hp (CoeffPair.toMax p φ)
  let W' := (CoeffPair.toMax p) ⁻¹' W
  have hoW' : IsOpen W' := hoW.preimage (CoeffPair.toMax p).continuous
  have hcW' : Convex ℝ W' :=
    hcW.linear_preimage ((CoeffPair.toMax p).toContinuousLinearMap.restrictScalars ℝ).toLinearMap
  have h0W' : (0 : CoeffPair p) ∈ W' := by simpa [W'] using h0W
  let N := max Nr Nc
  refine ⟨N,hNr.trans (le_max_left _ _),V ∩ W',hoV.inter hoW',hcV.inter hcW',
    ⟨hφV,hφW⟩,⟨h0V,h0W'⟩,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hξ,hη,hpair,_,ht⟩ := hr ψ hψ.1
  have hc : PeriodicCountingData hp (weightedBaseToPair SpectralWeight.one (unitWeightedPairEquiv ψ)) N := by
    rw [weightedBaseToPair_unitWeightedPairEquiv]
    exact hcount _ hψ.2 N (le_max_right _ _)
  obtain ⟨α,β,hab,hpres⟩ := exists_completePeriodicEndpointLabeling hp SpectralWeight.one
    (unitWeightedPairEquiv ψ) N hc ξ η hξ hη
    (fun n hn => hpair n (by dsimp [N] at hn; omega))
  refine ⟨α,β,by simpa only [weightedBaseToPair_unitWeightedPairEquiv] using hab,?_⟩
  intro K hK
  have heq : rootDisplacementPowerTail p K α β = rootDisplacementPowerTail p K ξ η := by
    funext n
    unfold rootDisplacementPowerTail
    split_ifs with hn
    · rw [(hpres n (by omega)).1,(hpres n (by omega)).2]
    · rfl
  rw [heq]
  exact ht K (by dsimp [N] at hK; omega)

end NLS.ZakharovShabat
