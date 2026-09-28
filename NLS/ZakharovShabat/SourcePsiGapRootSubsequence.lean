import NLS.ZakharovShabat.SourcePsiGapRootTailBound
import NLS.SequenceSpaces.UniformTailCompactness

/-!
# Subsequences of deleted roots trapped in converging periodic gaps

If source potentials converge and every retained root lies in its
assigned gap, endpoint bounds control the full deleted-root norms,
while uniform gap tails control their high modes. Finite Fourier
truncation compactness then yields a strongly convergent subsequence.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Gap-contained deleted roots over a convergent source sequence
have a norm-convergent subsequence in the deleted `ℓᵖ` space. -/
theorem exists_tendsto_subseq_deletedGapRoots_of_source_tendsto
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (ψ : ℕ → CoeffPair p)
    (hψ : Tendsto ψ atTop (𝓝 φ))
    (n : ℤ) (a : ℕ → DeletedCoeff p n)
    (hgap : ∀ k : ℕ, ∀ m : ℤ, m ≠ n →
      displacedRoots (a k : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 (ψ k) m) :
    ∃ b : DeletedCoeff p n, ∃ σ : ℕ → ℕ,
      StrictMono σ ∧ Tendsto (a ∘ σ) atTop (𝓝 b) := by
  obtain ⟨U,hUopen,_,hφU,_,R,hR,hdata⟩ :=
    exists_uniform_bounded_canonicalPeriodicDisplacements
      hp hp1 (periodOnePotential φ)
  let V : Set (CoeffPair p) := periodOnePotential ⁻¹' U
  have hVopen : IsOpen V :=
    hUopen.preimage (periodOnePotential (p := p)).continuous
  have hψV : ∀ᶠ k : ℕ in atTop, ψ k ∈ V :=
    hψ.eventually (hVopen.mem_nhds hφU)
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.1 hψV
  have hnorm (k : ℕ) (hk : K ≤ k) : ‖(a k : Coeff p)‖ ≤ 3*R := by
    let L := canonicalPeriodicLeftDisplacement hp hp1
      (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k))
    let Q := canonicalPeriodicRightDisplacement hp hp1
      (periodOnePotential (ψ k)) (periodOnePotential_mem (ψ k))
    let G := sourcePeriodicGapDisplacement hp hp1 (ψ k)
    obtain ⟨hL,hQ⟩ :=
      hdata (periodOnePotential (ψ k)) (hK k hk)
        (periodOnePotential_mem (ψ k))
    have hG : ‖G‖ ≤ 2*R := by
      have heq : G = Q-L := rfl
      rw [heq]
      have htri := norm_sub_le Q L
      linarith
    have ha := norm_deletedRoots_le_gap_displacements
      hp hp1 (ψ k) n (a k) (hgap k)
    change ‖(a k : Coeff p)‖ ≤ ‖L‖+‖G‖ at ha
    linarith
  have hbounded : Bornology.IsBounded
      (range (fun k : ℕ => (a k : Coeff p))) := by
    let initial : Set (Coeff p) :=
      (fun k : ℕ => (a k : Coeff p)) '' (Finset.range K : Set ℕ)
    have hinitial : initial.Finite :=
      (Finset.finite_toSet (Finset.range K)).image _
    have hsubset : range (fun k : ℕ => (a k : Coeff p)) ⊆
        initial ∪ closedBall 0 (3*R) := by
      intro x hx
      obtain ⟨k,rfl⟩ := hx
      by_cases hk : k < K
      · exact Or.inl ⟨k,Finset.mem_range.mpr hk,rfl⟩
      · right
        rw [mem_closedBall,dist_zero_right]
        exact hnorm k (Nat.le_of_not_gt hk)
    exact (hinitial.isBounded.union isBounded_closedBall).subset hsubset
  have htail : ∀ ε : ℝ, 0 < ε →
      ∃ s : Finset ℤ, ∃ N : ℕ,
        ∀ k : ℕ, N ≤ k →
          ‖(a k : Coeff p)-Coeff.truncate s (a k : Coeff p)‖ ≤ ε := by
    intro ε hε
    obtain ⟨M,W,hWopen,hφW,hWdata⟩ :=
      exists_uniform_small_deletedGapRoots_tails hp hp1 φ n hε
    have hψW : ∀ᶠ k : ℕ in atTop, ψ k ∈ W :=
      hψ.eventually (hWopen.mem_nhds hφW)
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 hψW
    refine ⟨Finset.Icc (-(M : ℤ)) M,N,?_⟩
    intro k hk
    exact hWdata (ψ k) (hN k hk) (a k) (hgap k) M le_rfl
  obtain ⟨bFull,σ,hσ,htend⟩ :=
    NLS.Coeff.exists_tendsto_subseq_of_bounded_uniform_tails
      (fun k : ℕ => (a k : Coeff p)) hbounded htail
  have hbmem : bFull ∈
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker :=
    (ContinuousLinearMap.isClosed_ker
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n)).mem_of_tendsto
      htend (Eventually.of_forall fun k => (a (σ k)).property)
  let b : DeletedCoeff p n := ⟨bFull,hbmem⟩
  have hconv : Tendsto (a ∘ σ) atTop (𝓝 b) := by
    apply (tendsto_subtype_rng).2
    exact htend
  exact ⟨b,σ,hσ,hconv⟩

end NLS.ZakharovShabat
