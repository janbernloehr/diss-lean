import NLS.ZakharovShabat.SourceRealTypeConvex

/-!
# The global almost-real source neighborhood of Lemma 10.1

Connected local source neighborhoods with common isolating discs cover
the real-type locus. Their union is connected because the real-type locus
is connected and each local neighborhood meets it at its center.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The straight spectral segment between the two canonical periodic
endpoints at a source potential. -/
def sourcePeriodicSegment (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) : Set ℂ :=
  segment ℝ
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)

/-- Containment of both periodic endpoints in an assigned disc implies
containment of the full straight periodic gap segment. -/
theorem sourcePeriodicSegment_subset_isolatingDisc
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ) (n : ℤ)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n) :
    sourcePeriodicSegment hp hp1 ψ n ⊆ sourceIsolatingDisc hp hp1 φ N ε n := by
  have hconv : Convex ℝ (sourceIsolatingDisc hp hp1 φ N ε n) := by
    unfold sourceIsolatingDisc
    split <;> exact convex_ball _ _
  exact hconv.segment_subset (hcluster (Or.inl rfl))
    (hcluster (Or.inr (Or.inl rfl)))

/-- A union of connected sets is connected when every set meets a common
connected spine contained in the union. -/
private theorem connected_union_along_spine {α ι : Type*} [TopologicalSpace α]
    (S : Set α) (U : ι → Set α)
    (hS : IsConnected S) (hU : ∀ i, IsConnected (U i))
    (hmeet : ∀ i, (S ∩ U i).Nonempty)
    (hsub : S ⊆ ⋃ i, U i) : IsConnected (⋃ i, U i) := by
  have hfamily (i : ι) : IsConnected (S ∪ U i) :=
    hS.union (hmeet i) (hU i)
  have hcommon : (⋂ i, S ∪ U i).Nonempty := by
    obtain ⟨x, hx⟩ := hS.nonempty
    exact ⟨x, mem_iInter.mpr (fun i => Or.inl hx)⟩
  have hpre : IsPreconnected (⋃ i, S ∪ U i) :=
    isPreconnected_iUnion hcommon (fun i => (hfamily i).isPreconnected)
  have heq : (⋃ i, S ∪ U i) = ⋃ i, U i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rcases hi with hs | hu
      · exact hsub hs
      · exact mem_iUnion_of_mem i hu
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion_of_mem i (Or.inr hi)
  rw [heq] at hpre
  exact ⟨(hS.nonempty.mono hsub), hpre⟩

/-- Lemma 10.1 for finite source exponents: an open connected
neighborhood of the entire real-type locus. Every point has an open
connected neighborhood carrying one common sequence of pairwise disjoint
isolating discs for all five canonical spectral coordinates. -/
theorem exists_global_source_isolating_neighborhood
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧
        ψ ∈ V ∧ V ⊆ W ∧
        ∃ φ : CoeffPair p, ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
          (∀ χ ∈ V, ∀ n : ℤ,
            sourceSpectralCluster hp hp1 χ n ⊆
              sourceIsolatingDisc hp hp1 φ N ε n) ∧
          (∀ χ ∈ V, ∀ n : ℤ,
            sourcePeriodicSegment hp hp1 χ n ⊆
              sourceIsolatingDisc hp hp1 φ N ε n) ∧
          (∀ i j : ℤ, i ≠ j →
            Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
              (sourceIsolatingDisc hp hp1 φ N ε j)) := by
  classical
  let R := {φ : CoeffPair p // φ ∈ realTypeSourceLocus p}
  have hloc : ∀ x : R, ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ x.val ∈ U ∧
        (∀ ψ ∈ U, ∀ n : ℤ,
          sourceSpectralCluster hp hp1 ψ n ⊆
            sourceIsolatingDisc hp hp1 x.val N ε n) ∧
        (∀ i j : ℤ, i ≠ j →
          Disjoint (sourceIsolatingDisc hp hp1 x.val N ε i)
            (sourceIsolatingDisc hp hp1 x.val N ε j)) := by
    intro x
    exact exists_local_source_connected_isolating_discs hp hp1 x.val x.property
  choose N ε hε hεmax U hUopen hUconnected hxU hcluster hdisjoint using hloc
  let W : Set (CoeffPair p) := ⋃ x : R, U x
  have hWopen : IsOpen W := isOpen_iUnion fun x => hUopen x
  have hRsub : realTypeSourceLocus p ⊆ W := by
    intro φ hφ
    exact mem_iUnion_of_mem (⟨φ, hφ⟩ : R) (hxU ⟨φ, hφ⟩)
  have hWconnected : IsConnected W :=
    connected_union_along_spine (realTypeSourceLocus p) U
      isConnected_realTypeSourceLocus hUconnected
      (fun x => ⟨x.val, x.property, hxU x⟩) hRsub
  refine ⟨W, hWopen, hWconnected, hRsub, ?_⟩
  intro ψ hψ
  obtain ⟨x, hx⟩ := mem_iUnion.mp hψ
  refine ⟨U x, hUopen x, hUconnected x, hx,
    (fun χ hχ => mem_iUnion_of_mem x hχ), x.val, N x, ε x,
    hε x, hεmax x, hcluster x, ?_, hdisjoint x⟩
  intro χ hχ n
  exact sourcePeriodicSegment_subset_isolatingDisc hp hp1 x.val χ (N x) (ε x) n
    (hcluster x χ hχ n)

end NLS.ZakharovShabat
