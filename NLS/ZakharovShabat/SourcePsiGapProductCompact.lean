import NLS.ZakharovShabat.SourcePsiGapRootTailBound
import NLS.ZakharovShabat.SourcePsiGapRootMap
import NLS.ZakharovShabat.SourcePsiDeletedRootFill
import NLS.ZakharovShabat.SourceStandardRootContourLocalStability
import NLS.SequenceSpaces.UniformTailCompactness
import Mathlib.Topology.Sequences

/-!
# Compact product of periodic gaps in the coefficient space

The product of the shifted periodic gaps is compact in `ℓᵖ` for
`1 < p < ∞`. Pointwise gap placement gives a common `ℓᵖ` majorant
from the left endpoint and gap-length displacements. The majorant
controls both full norms and tails, while closedness of each gap
preserves placement under strong limits.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Full coefficient sequences with every displaced root in its
corresponding closed periodic gap. This is the ambient `ℓᵖ`
realization of the gap product used in Lemma 12.10. -/
def sourcePeriodicGapRootSet
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) : Set (Coeff p) :=
  {a | ∀ m : ℤ,
    displacedRoots a m ∈ sourcePeriodicSegment hp hp1 ψ m}

/-- A gap-contained full root sequence has tails bounded by the
left-endpoint and gap-length displacement tails. -/
theorem norm_gapRoot_sub_truncate_le_gap_tails
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (a : Coeff p) (ha : a ∈ sourcePeriodicGapRootSet hp hp1 ψ)
    (s : Finset ℤ) :
    ‖a-Coeff.truncate s a‖ ≤
      ‖canonicalPeriodicLeftDisplacement hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) -
          Coeff.truncate s (canonicalPeriodicLeftDisplacement hp hp1
            (periodOnePotential ψ) (periodOnePotential_mem ψ))‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ -
        Coeff.truncate s (sourcePeriodicGapDisplacement hp hp1 ψ)‖ := by
  apply Coeff.norm_sub_truncate_le_of_pointwise_norm_le_add
    (canonicalPeriodicLeftDisplacement hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ))
    (sourcePeriodicGapDisplacement hp hp1 ψ) a s
  intro m _
  have hbound := norm_sourcePeriodicSegment_sample_sub_free_le
    hp hp1 ψ m (displacedRoots a m) (ha m)
  simpa only [displacedRoots,add_sub_cancel_left] using hbound

/-- The full gap product is bounded in the coefficient norm. -/
theorem norm_gapRoot_le_gap_displacements
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (a : Coeff p) (ha : a ∈ sourcePeriodicGapRootSet hp hp1 ψ) :
    ‖a‖ ≤
      ‖canonicalPeriodicLeftDisplacement hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ)‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ := by
  simpa using norm_gapRoot_sub_truncate_le_gap_tails
    hp hp1 ψ a ha ∅

/-- The full product of periodic gaps is compact in `ℓᵖ`. -/
theorem isCompact_sourcePeriodicGapRootSet
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    IsCompact (sourcePeriodicGapRootSet hp hp1 ψ) := by
  apply isCompact_iff_isSeqCompact.mpr
  intro a ha
  let L := canonicalPeriodicLeftDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let G := sourcePeriodicGapDisplacement hp hp1 ψ
  have hbounded : Bornology.IsBounded (range a) := by
    apply (isBounded_closedBall : Bornology.IsBounded
      (closedBall (0 : Coeff p) (‖L‖ + ‖G‖))).subset
    intro x hx
    obtain ⟨j,rfl⟩ := hx
    rw [mem_closedBall,dist_zero_right]
    exact norm_gapRoot_le_gap_displacements hp hp1 ψ (a j) (ha j)
  have htail : ∀ ε : ℝ, 0 < ε →
      ∃ s : Finset ℤ, ∃ N : ℕ,
        ∀ j : ℕ, N ≤ j →
          ‖a j-Coeff.truncate s (a j)‖ ≤ ε := by
    intro ε hε
    obtain ⟨sL,hsL⟩ :=
      Metric.tendsto_atTop.mp (Coeff.tendsto_truncate hp L)
        (ε/2) (half_pos hε)
    obtain ⟨sG,hsG⟩ :=
      Metric.tendsto_atTop.mp (Coeff.tendsto_truncate hp G)
        (ε/2) (half_pos hε)
    let s := sL ∪ sG
    have hL : ‖L-Coeff.truncate s L‖ ≤ ε/2 := by
      have h := hsL s (Finset.subset_union_left)
      rw [dist_eq_norm] at h
      simpa only [norm_sub_rev] using le_of_lt h
    have hG : ‖G-Coeff.truncate s G‖ ≤ ε/2 := by
      have h := hsG s (Finset.subset_union_right)
      rw [dist_eq_norm] at h
      simpa only [norm_sub_rev] using le_of_lt h
    refine ⟨s,0,?_⟩
    intro j _
    have hj := norm_gapRoot_sub_truncate_le_gap_tails
      hp hp1 ψ (a j) (ha j) s
    change ‖a j-Coeff.truncate s (a j)‖ ≤
      ‖L-Coeff.truncate s L‖ + ‖G-Coeff.truncate s G‖ at hj
    linarith
  obtain ⟨b,σ,hσ,hb⟩ :=
    NLS.Coeff.exists_tendsto_subseq_of_bounded_uniform_tails
      a hbounded htail
  refine ⟨b,?_,σ,hσ,hb⟩
  intro m
  have heval : Continuous (fun x : Coeff p => x m) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).continuous
  have hroot : Continuous (fun x : Coeff p => displacedRoots x m) := by
    change Continuous (fun x : Coeff p => (Real.pi : ℂ)*m + x m)
    exact continuous_const.add heval
  exact (isClosed_sourcePeriodicSegment hp hp1 ψ m).mem_of_tendsto
    (hroot.continuousAt.tendsto.comp hb)
    (Filter.Eventually.of_forall fun j => ha (σ j) m)

/-- Filling the omitted coordinate of the canonical gap-root vector
with the periodic midpoint puts it in the compact full gap product. -/
theorem sourcePsiGapRoot_filled_mem_periodicGapRootSet
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (n : ℤ) :
    sourcePsiFillDeletedRoot n (sourcePsiGapRoot hp hp1 n φ)
      (sourceStandardRootMidpoint hp hp1 φ.val n) ∈
        sourcePeriodicGapRootSet hp hp1 φ.val := by
  intro m
  by_cases hmn : m = n
  · subst m
    rw [displacedRoots_sourcePsiFillDeletedRoot_same]
    simpa only [sourceStandardRootMidpoint] using
      sourcePeriodicMidpoint_mem_segment hp hp1 φ.val n
  · rw [displacedRoots_sourcePsiFillDeletedRoot_other n m hmn]
    exact sourcePsiGapRoot_mem_periodicSegment hp hp1 n m hmn φ

end NLS.ZakharovShabat
