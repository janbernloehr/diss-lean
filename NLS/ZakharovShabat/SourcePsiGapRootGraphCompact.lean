import NLS.ZakharovShabat.SourcePsiGapRootIsolation

/-!
# Compactness of gap-root graphs

Over a compact set of real-type source potentials, every sequence of
gap-contained deleted-root vectors has a convergent subsequence whose
source and root limits remain in the graph. This packages the uniform
tail estimate and moving-gap closedness as a properness statement for
the projection onto source potentials.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The graph of deleted-root vectors placed in the periodic gaps over
a compact real-type source set is compact. -/
theorem isCompact_deletedGapRootGraph_over_compact_realTypeSources
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (K : Set (CoeffPair p)) (hK : IsCompact K)
    (hKreal : ∀ φ ∈ K, IsRealType (CoeffPair.toMax p φ)) :
    IsCompact {t : CoeffPair p × DeletedCoeff p n |
      t.1 ∈ K ∧ ∀ m : ℤ, m ≠ n →
        displacedRoots (t.2 : Coeff p) m ∈
          sourcePeriodicSegment hp hp1 t.1 m} := by
  apply IsSeqCompact.isCompact
  intro t ht
  obtain ⟨φ,hφK,σ,hσ,hφ⟩ :=
    hK.tendsto_subseq (fun k => (ht k).1)
  let ψ : ℕ → CoeffPair p := fun k => (t (σ k)).1
  let a : ℕ → DeletedCoeff p n := fun k => (t (σ k)).2
  have hψ : Tendsto ψ atTop (𝓝 φ) := hφ
  have hgap : ∀ k : ℕ, ∀ m : ℤ, m ≠ n →
      displacedRoots (a k : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 (ψ k) m := by
    intro k m hmn
    exact (ht (σ k)).2 m hmn
  obtain ⟨b,τ,hτ,hb,hbgap⟩ :=
    exists_tendsto_subseq_deletedGapRoots_mem_limit_segments
      hp hp1 φ (hKreal φ hφK) ψ hψ n a hgap
  refine ⟨(φ,b),⟨hφK,hbgap⟩,σ ∘ τ,hσ.comp hτ,?_⟩
  have hsource : Tendsto (ψ ∘ τ) atTop (𝓝 φ) :=
    hψ.comp hτ.tendsto_atTop
  have hpair := hsource.prodMk_nhds hb
  simpa only [Function.comp_def,ψ,a] using hpair

/-- For a fixed real-type source, the entire family of deleted-root
vectors with retained roots in their assigned gaps is compact. -/
theorem isCompact_deletedGapRoots_at_realTypeSource
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    IsCompact {a : DeletedCoeff p n | ∀ m : ℤ, m ≠ n →
      displacedRoots (a : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 φ m} := by
  apply IsSeqCompact.isCompact
  intro a ha
  obtain ⟨b,σ,hσ,hb,hbgap⟩ :=
    exists_tendsto_subseq_deletedGapRoots_mem_limit_segments
      hp hp1 φ hφ (fun _ => φ) tendsto_const_nhds n a
        (fun k m hmn => ha k m hmn)
  exact ⟨b,hbgap,σ,hσ,hb⟩

end NLS.ZakharovShabat
