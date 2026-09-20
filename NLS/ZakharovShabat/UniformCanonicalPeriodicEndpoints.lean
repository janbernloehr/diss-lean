import NLS.ZakharovShabat.CanonicalPeriodicEndpoints

/-!
# Common local cutoffs for canonical periodic endpoints

The ordered existence theorem supplies labelings on one neighborhood at
every large cutoff. Cutoff-independent uniqueness identifies all of them
with the same canonical endpoint functions.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On one potential neighborhood, the fixed canonical endpoints are valid at every large cutoff. -/
theorem exists_uniform_canonicalPeriodicEndpoints (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∀ hψ : weightedBaseToPair w ψ ∈ pairParitySubspace 0, ∀ N : ℕ, N₀ ≤ N →
          PeriodicEndpointLabeling hp (weightedBaseToPair w ψ) N
            (canonicalPeriodicLeft hp hp1 (weightedBaseToPair w ψ) hψ)
            (canonicalPeriodicRight hp hp1 (weightedBaseToPair w ψ) hψ) := by
  obtain ⟨N₀,hN,U,ho,hc,hφ,h0,h⟩ := exists_uniform_orderedPeriodicEndpoints hp hp1 w φ
  refine ⟨N₀,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ heven N hN
  obtain ⟨ξ,η,hl,hw,hs⟩ := h ψ hψ heven N hN
  obtain ⟨hx,hy⟩ := hl.eq_canonicalPeriodicEndpoints hp1 heven hw hs
  simpa only [hx,hy] using hl

/-- A common nearby cutoff can be chosen above any prescribed finite index block. -/
theorem exists_eventually_canonicalPeriodicEndpointLabeling_above (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (K : ℕ) :
    ∃ N : ℕ, K ≤ N ∧ 2 ≤ N ∧ ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      PeriodicEndpointLabeling hp ψ.val N
        (canonicalPeriodicLeft hp hp1 ψ.val ψ.property) (canonicalPeriodicRight hp hp1 ψ.val ψ.property) := by
  let L : PairSpace p →L[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight p := unitBaseEquiv.symm.toContinuousLinearMap
  have he (ψ : PairSpace p) : weightedBaseToPair SpectralWeight.one (L ψ) = ψ := by
    rw [← unitBaseEquiv_eq]
    exact unitBaseEquiv.apply_symm_apply ψ
  obtain ⟨N,hN,U,ho,_,hφ,_,h⟩ := exists_uniform_canonicalPeriodicEndpoints hp hp1 SpectralWeight.one (L φ.val)
  have hc : Continuous (fun ψ : pairParitySubspace (p := p) 0 => L ψ.val) := L.continuous.comp continuous_subtype_val
  have hu : ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ, L ψ.val ∈ U :=
    hc.continuousAt.eventually (ho.mem_nhds hφ)
  refine ⟨max N K,le_max_right _ _,hN.trans (le_max_left _ _),?_⟩
  filter_upwards [hu] with ψ hψ
  have hh : ∀ hχ : weightedBaseToPair SpectralWeight.one (L ψ.val) ∈ pairParitySubspace 0,
      PeriodicEndpointLabeling hp (weightedBaseToPair SpectralWeight.one (L ψ.val)) (max N K)
        (canonicalPeriodicLeft hp hp1 _ hχ) (canonicalPeriodicRight hp hp1 _ hχ) :=
    fun hχ => h (L ψ.val) hψ hχ (max N K) (le_max_left _ _)
  rw [he] at hh
  exact hh ψ.property

/-- Nearby even potentials have canonical endpoint labelings at one common cutoff. -/
theorem exists_eventually_canonicalPeriodicEndpointLabeling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      PeriodicEndpointLabeling hp ψ.val N
        (canonicalPeriodicLeft hp hp1 ψ.val ψ.property) (canonicalPeriodicRight hp hp1 ψ.val ψ.property) := by
  obtain ⟨N,_,hN,h⟩ := exists_eventually_canonicalPeriodicEndpointLabeling_above hp hp1 φ 0
  exact ⟨N,hN,h⟩

end NLS.ZakharovShabat
