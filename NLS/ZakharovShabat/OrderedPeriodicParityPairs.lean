import NLS.ZakharovShabat.CentralParityOrdering
import NLS.ZakharovShabat.PeriodicEndpointOrder

/-! # Globally ordered separate parity lists with full original multiplicities -/
noncomputable section
set_option autoImplicit false
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Swapping a resonant pair retains its original spectrum, multiplicity and quantitative data. -/
theorem PeriodicResonantPair.swap {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {n : ℤ} {x y : ℂ}
    (h : PeriodicResonantPair hp w φ n x y) : PeriodicResonantPair hp w φ n y x := by
  refine ⟨h.right_mem,h.left_mem,fun z hz => (h.spectrum_iff z hz).trans or_comm,?_,
    h.analyticOrder_eq_multiplicity,?_,?_,h.right_bound,h.left_bound,?_⟩
  · intro z hz
    rw [h.multiplicity_eq_count z hz,Multiset.pair_comm]
  · simpa only [add_comm] using h.midpoint_eq
  · rw [h.squaredGap_eq]
    ring
  · simpa only [norm_sub_rev] using h.gap_le

/-- Sorting a resonant pair retains all of its original operator information. -/
theorem PeriodicResonantPair.ordered {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {n : ℤ} {x y : ℂ}
    (h : PeriodicResonantPair hp w φ n x y) :
    PeriodicResonantPair hp w φ n (orderedEndpointLeft x y) (orderedEndpointRight x y) := by
  unfold orderedEndpointLeft orderedEndpointRight
  split_ifs
  · exact h
  · exact h.swap

/-- Pairwise ordering preserves both central parity multisets and all distant root data. -/
theorem CompletePeriodicParityPairs.ordered_pairs {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) :
    CompletePeriodicParityPairs hp w φ N (fun n => orderedEndpointLeft (ξ n) (η n))
      (fun n => orderedEndpointRight (ξ n) (η n)) := by
  have hlp := memℓp_orderedEndpoint_displacements ξ η (fun n => (Real.pi : ℂ)*n)
    h.left_displacement h.right_displacement
  refine ⟨h.counting,h.even_potential,hlp.1,hlp.2,⟨?_,?_⟩,fun n hn => (h.distant n hn).ordered⟩
  · simpa only [orderedEndpointPair_multiset] using h.central.even
  · simpa only [orderedEndpointPair_multiset] using h.central.odd

/-- Replacing the central labels by any exact parity enumeration retains the complete data. -/
theorem CompletePeriodicParityPairs.relabel_central {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (a b : ℤ → ℂ)
    (hc : CentralParityLabeling hp (weightedBaseToPair w φ) N a b) :
    CompletePeriodicParityPairs hp w φ N (spliceCentralRoots N a ξ) (spliceCentralRoots N b η) := by
  refine ⟨h.counting,h.even_potential,memℓp_spliceCentralRoots N a ξ h.left_displacement,
    memℓp_spliceCentralRoots N b η h.right_displacement,hc.splice ξ η,?_⟩
  intro n hn
  simpa only [spliceCentralRoots,if_pos hn] using h.distant n hn

/-- Both parity subsequences can be globally sorted independently, with actual central
multiplicities and unchanged distant pair multisets. No real-type premise is needed. -/
theorem CompletePeriodicParityPairs.exists_parity_ordered {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) :
    ∃ α β : ℤ → ℂ, CompletePeriodicParityPairs hp w φ N α β ∧
      (∀ n, complexLexLE (α n) (β n)) ∧
      (∀ i j : ℤ, i < j → i % 2 = j % 2 → complexLexLE (β i) (α j)) ∧
      ∀ n : ℤ, N < n.natAbs → ({α n,β n} : Multiset ℂ) = {ξ n,η n} := by
  obtain ⟨a,b,hc,ho⟩ := exists_ordered_centralParityLabeling hp _ h.even_potential N h.counting
  let α := spliceCentralRoots N a (fun n => orderedEndpointLeft (ξ n) (η n))
  let β := spliceCentralRoots N b (fun n => orderedEndpointRight (ξ n) (η n))
  have hnew : CompletePeriodicParityPairs hp w φ N α β := h.ordered_pairs.relabel_central a b hc
  have hmem (n : ℤ) (hn : n.natAbs ≤ N) : n ∈ centralParityIndices N (n % 2) := by
    simp only [centralParityIndices,Finset.mem_filter,Finset.mem_Icc]
    omega
  refine ⟨α,β,hnew,?_,?_,?_⟩
  · intro n
    by_cases hn : N < n.natAbs
    · simpa only [α,β,spliceCentralRoots,if_pos hn] using orderedEndpointPair_le (ξ n) (η n)
    · have hnN : n.natAbs ≤ N := by omega
      simpa only [α,β,spliceCentralRoots,if_neg hn] using
        (ho (n % 2) (by omega)).1 n (hmem n hnN)
  · intro i j hij hpij
    by_cases hi : i.natAbs ≤ N
    · by_cases hj : j.natAbs ≤ N
      · have hjmem : j ∈ centralParityIndices N (i % 2) := by rw [hpij]; exact hmem j hj
        simpa only [α,β,spliceCentralRoots,if_neg (by omega : ¬N < i.natAbs),
          if_neg (by omega : ¬N < j.natAbs)] using
            (ho (i % 2) (by omega)).2 i (hmem i hi) j hjmem hij
      · exact complexLexLE_of_re_lt (hnew.toEndpoints.re_lt_of_distant i j hij
          (Or.inr (by omega)) _ _ (Or.inr rfl) (Or.inl rfl))
    · exact complexLexLE_of_re_lt (hnew.toEndpoints.re_lt_of_distant i j hij
        (Or.inl (by omega)) _ _ (Or.inr rfl) (Or.inl rfl))
  · intro n hn
    simp only [α,β,spliceCentralRoots,if_pos hn,orderedEndpointPair_multiset]

/-- Every even potential has separate globally ordered parity lists with full counted root data. -/
theorem exists_ordered_completePeriodicParityPairs (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    (hφ : weightedBaseToPair w φ ∈ pairParitySubspace 0) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ, CompletePeriodicParityPairs hp w φ N ξ η ∧
      (∀ n, complexLexLE (ξ n) (η n)) ∧
      ∀ i j : ℤ, i < j → i % 2 = j % 2 → complexLexLE (η i) (ξ j) := by
  obtain ⟨N,_,U,_,_,hU,_,h⟩ := exists_uniform_completePeriodicParityPairs hp hp1 w φ
  obtain ⟨ξ,η,hd⟩ := h φ hU hφ N le_rfl
  obtain ⟨a,b,hab,hw,ho,_⟩ := hd.exists_parity_ordered
  exact ⟨N,a,b,hab,hw,ho⟩

end NLS.ZakharovShabat
