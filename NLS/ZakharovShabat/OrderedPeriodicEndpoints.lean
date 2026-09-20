import NLS.ZakharovShabat.PeriodicEndpointOrder
import NLS.ZakharovShabat.RealType

/-!
# Globally ordered complete periodic endpoints

Sort the full central multiset and each distant pair. Separation of the
free discs gives global order, with every original multiplicity and both
lp displacements retained. The distant pairs are unchanged as multisets.
Identifying the ordered central pairs' parity requires a further argument.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Complete periodic endpoints can be globally ordered without altering any distant pair multiset. -/
theorem PeriodicEndpointLabeling.exists_ordered {hp : p ≠ ⊤} {φ : PairSpace p}
    {N : ℕ} {ξ η : ℤ → ℂ} (h : PeriodicEndpointLabeling hp φ N ξ η) :
    ∃ α β : ℤ → ℂ, PeriodicEndpointLabeling hp φ N α β ∧
      (∀ n, complexLexLE (α n) (β n)) ∧
      (∀ i j : ℤ, i < j → complexLexLE (β i) (α j)) ∧
      ∀ n : ℤ, N < n.natAbs → ({α n,β n} : Multiset ℂ) = {ξ n,η n} := by
  obtain ⟨a,b,hc,hw,ho⟩ := exists_ordered_centralPeriodicLabeling hp φ N h.counting
  let α := spliceCentralRoots N a (fun n => orderedEndpointLeft (ξ n) (η n))
  let β := spliceCentralRoots N b (fun n => orderedEndpointRight (ξ n) (η n))
  have hnew : PeriodicEndpointLabeling hp φ N α β := h.ordered_pairs.relabel_central a b hc
  refine ⟨α,β,hnew,?_,?_,?_⟩
  · intro n
    by_cases hn : N < n.natAbs
    · simpa only [α,β,spliceCentralRoots,if_pos hn] using orderedEndpointPair_le (ξ n) (η n)
    · simpa only [α,β,spliceCentralRoots,if_neg hn] using hw n (by omega)
  · intro i j hij
    by_cases hi : i.natAbs ≤ N
    · by_cases hj : j.natAbs ≤ N
      · simpa only [α,β,spliceCentralRoots,if_neg (by omega : ¬N < i.natAbs),
          if_neg (by omega : ¬N < j.natAbs)] using ho i hi j hj hij
      · exact complexLexLE_of_re_lt (hnew.re_lt_of_distant i j hij (Or.inr (by omega)) _ _ (Or.inr rfl) (Or.inl rfl))
    · exact complexLexLE_of_re_lt (hnew.re_lt_of_distant i j hij (Or.inl (by omega)) _ _ (Or.inr rfl) (Or.inl rfl))
  · intro n hn
    simp only [α,β,spliceCentralRoots,if_pos hn,orderedEndpointPair_multiset]

/-- One neighborhood supplies ordered complete endpoint labelings at every sufficiently large cutoff. -/
theorem exists_uniform_orderedPeriodicEndpoints (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        weightedBaseToPair w ψ ∈ pairParitySubspace 0 → ∀ N : ℕ, N₀ ≤ N →
          ∃ ξ η : ℤ → ℂ, PeriodicEndpointLabeling hp (weightedBaseToPair w ψ) N ξ η ∧
            (∀ n, complexLexLE (ξ n) (η n)) ∧
            ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j) := by
  obtain ⟨N₀,hN,U,ho,hc,hφ,h0,h⟩ := exists_uniform_completePeriodicParityPairs hp hp1 w φ
  refine ⟨N₀,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ heven N hN
  obtain ⟨ξ,η,hpairs⟩ := h ψ hψ heven N hN
  obtain ⟨α,β,hα,hw,hs,_⟩ := hpairs.toEndpoints.exists_ordered
  exact ⟨α,β,hα,hw,hs⟩

/-- Every even potential at finite p>1 has a globally ordered complete periodic endpoint sequence. -/
theorem exists_ordered_periodicEndpointLabeling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ, PeriodicEndpointLabeling hp φ N ξ η ∧
      (∀ n, complexLexLE (ξ n) (η n)) ∧ ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j) := by
  obtain ⟨N,_,U,_,_,hU,_,h⟩ := exists_uniform_orderedPeriodicEndpoints hp hp1 SpectralWeight.one
    (unitBaseEquiv.symm φ)
  have he : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq, ContinuousLinearEquiv.apply_symm_apply]
  obtain ⟨ξ,η,hl,hw,hs⟩ := h _ hU (by rw [he]; exact hφ) N le_rfl
  exact ⟨N,ξ,η,by simpa only [he] using hl,hw,hs⟩

/-- Both endpoint coordinates are real at real-type potentials, for every central and distant index. -/
theorem PeriodicEndpointLabeling.roots_im_eq_zero_of_realType {hp : p ≠ ⊤}
    {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ} (h : PeriodicEndpointLabeling hp φ N ξ η)
    (hreal : IsRealType φ) (n : ℤ) : (ξ n).im = 0 ∧ (η n).im = 0 :=
  ⟨periodicSpectrum_im_eq_zero_of_realType hp φ hreal _ ((h.exhaustive _).mpr ⟨n,Or.inl rfl⟩),
    periodicSpectrum_im_eq_zero_of_realType hp φ hreal _ ((h.exhaustive _).mpr ⟨n,Or.inr rfl⟩)⟩

end NLS.ZakharovShabat
