import NLS.ZakharovShabat.SourcePsiGapRootMap
import NLS.ZakharovShabat.SourcePsiGapRootTailBound
import NLS.ZakharovShabat.SourceStandardRootContourLocalStability
import NLS.SequenceSpaces.UniformTailCompactness

/-!
# Compactness of deleted gap roots as the omitted index escapes

The gap displacement bounds are uniform in the omitted index. Hence
any sequence of gap-contained deleted-root vectors has a strongly
converging subsequence in the ambient coefficient space. When the
omitted indices escape, every fixed coordinate is eventually retained,
so each limiting displaced root remains in its periodic gap.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Gap-contained deleted roots with an escaping omitted index admit
a strongly converging ambient subsequence whose every root stays in
its assigned periodic gap. -/
theorem exists_tendsto_subseq_deletedGapRoots_varyingIndex
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℕ → ℤ)
    (hn : Tendsto (fun j : ℕ => (n j).natAbs) atTop atTop)
    (a : ∀ j : ℕ, DeletedCoeff p (n j))
    (hgap : ∀ (j : ℕ) (m : ℤ), m ≠ n j →
      displacedRoots (a j : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 ψ m) :
    ∃ b : Coeff p, ∃ σ : ℕ → ℕ,
      StrictMono σ ∧
      Tendsto (fun j : ℕ => (a (σ j) : Coeff p)) atTop (𝓝 b) ∧
      ∀ m : ℤ,
        displacedRoots b m ∈ sourcePeriodicSegment hp hp1 ψ m := by
  let L := canonicalPeriodicLeftDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let G := sourcePeriodicGapDisplacement hp hp1 ψ
  have hnorm (j : ℕ) : ‖(a j : Coeff p)‖ ≤ ‖L‖ + ‖G‖ :=
    norm_deletedRoots_le_gap_displacements hp hp1 ψ (n j) (a j) (hgap j)
  have hbounded : Bornology.IsBounded
      (range (fun j : ℕ => (a j : Coeff p))) := by
    apply (isBounded_closedBall : Bornology.IsBounded
      (closedBall (0 : Coeff p) (‖L‖ + ‖G‖))).subset
    intro x hx
    obtain ⟨j,rfl⟩ := hx
    rw [mem_closedBall,dist_zero_right]
    exact hnorm j
  have htail : ∀ ε : ℝ, 0 < ε →
      ∃ s : Finset ℤ, ∃ N : ℕ,
        ∀ j : ℕ, N ≤ j →
          ‖(a j : Coeff p)-Coeff.truncate s (a j : Coeff p)‖ ≤ ε := by
    intro ε hε
    obtain ⟨M,V,_,hψV,hV⟩ :=
      exists_uniform_small_deletedGapRoots_tails_allIndices hp hp1 ψ hε
    refine ⟨Finset.Icc (-(M : ℤ)) M,0,?_⟩
    intro j _
    exact hV ψ hψV (n j) (a j) (hgap j) M le_rfl
  obtain ⟨b,σ,hσ,hb⟩ :=
    NLS.Coeff.exists_tendsto_subseq_of_bounded_uniform_tails
      (fun j : ℕ => (a j : Coeff p)) hbounded htail
  refine ⟨b,σ,hσ,hb,?_⟩
  intro m
  have hne : ∀ᶠ j : ℕ in atTop, m ≠ n (σ j) := by
    have hlarge := (hn.comp hσ.tendsto_atTop).eventually_ge_atTop
      (m.natAbs + 1)
    filter_upwards [hlarge] with j hj hmeq
    dsimp only [Function.comp_def] at hj
    subst m
    omega
  have hplaced : ∀ᶠ j : ℕ in atTop,
      displacedRoots (a (σ j) : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 ψ m := by
    filter_upwards [hne] with j hj
    exact hgap (σ j) m hj
  have heval : Continuous (fun x : Coeff p => x m) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).continuous
  have hroot : Continuous (fun x : Coeff p => displacedRoots x m) := by
    change Continuous (fun x : Coeff p => (Real.pi : ℂ)*m + x m)
    exact continuous_const.add heval
  exact (isClosed_sourcePeriodicSegment hp hp1 ψ m).mem_of_tendsto
    (hroot.continuousAt.tendsto.comp hb) hplaced

/-- The canonical gap-root vectors at indices escaping in absolute
value always have a strongly converging subsequence in `ℓᵖ`; every
coordinate of its limit is gap-contained. -/
theorem exists_tendsto_subseq_sourcePsiGapRoot_varyingIndex
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (n : ℕ → ℤ)
    (hn : Tendsto (fun j : ℕ => (n j).natAbs) atTop atTop) :
    ∃ b : Coeff p, ∃ σ : ℕ → ℕ,
      StrictMono σ ∧
      Tendsto (fun j : ℕ =>
        (sourcePsiGapRoot hp hp1 (n (σ j)) φ : Coeff p)) atTop (𝓝 b) ∧
      ∀ m : ℤ,
        displacedRoots b m ∈ sourcePeriodicSegment hp hp1 φ.val m := by
  exact exists_tendsto_subseq_deletedGapRoots_varyingIndex
    hp hp1 φ.val n hn
    (fun j => sourcePsiGapRoot hp hp1 (n j) φ)
    (fun j m hm => sourcePsiGapRoot_mem_periodicSegment hp hp1 (n j) m hm φ)

end NLS.ZakharovShabat
