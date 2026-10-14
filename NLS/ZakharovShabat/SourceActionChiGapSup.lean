import NLS.ZakharovShabat.SourceActionChiGapIntegral
import NLS.ZakharovShabat.SourceFiniteGapExterior

/-!
# The literal gap supremum in the proof of Theorem 11.2

The selected segment is compact and the deleted product is analytic
through it on the original domain. Thus the supremum is finite, including
at collapsed complex gaps, and bounds every point of the actual gap.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal supremum over the actual, possibly collapsed complex gap. -/
def sourceActionChiGapSup (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) : ℝ :=
  sSup ((fun z => ‖sourceActionChi hp hp1 n ψ z-1‖) '' sourcePeriodicSegment hp hp1 ψ n)

/-- The deleted product is continuous through the entire selected segment. -/
theorem SourceEquation2_18Data.chi_continuousOn_gap
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    ContinuousOn (sourceActionChi hp hp1 n ψ) (sourcePeriodicSegment hp hp1 ψ n) := by
  apply (H.joint n).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
  exact fun z hz => ⟨hψ,H.segment_subset_omitted ψ hψ n hz⟩

theorem SourceEquation2_18Data.chiGapSup_bddAbove
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    BddAbove ((fun z => ‖sourceActionChi hp hp1 n ψ z-1‖) '' sourcePeriodicSegment hp hp1 ψ n) :=
  ((isCompact_sourcePeriodicSegment hp hp1 ψ n).image_of_continuousOn
    ((H.chi_continuousOn_gap ψ hψ n).sub continuousOn_const).norm).bddAbove

/-- Every value on the actual gap is bounded by its finite supremum. -/
theorem SourceEquation2_18Data.norm_chi_sub_one_le_gapSup
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ n) :
    ‖sourceActionChi hp hp1 n ψ z-1‖ ≤ sourceActionChiGapSup hp hp1 ψ n :=
  le_csSup (H.chiGapSup_bddAbove ψ hψ n) ⟨z,hz,rfl⟩

theorem SourceEquation2_18Data.chiGapSup_nonneg
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    0 ≤ sourceActionChiGapSup hp hp1 ψ n :=
  (norm_nonneg _).trans (H.norm_chi_sub_one_le_gapSup ψ hψ n _
    (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n))

/-- A bound on every gap point bounds the literal supremum, with no real-source assumption. -/
theorem sourceActionChiGapSup_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (b : ℝ)
    (hb : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n, ‖sourceActionChi hp hp1 n ψ z-1‖ ≤ b) :
    sourceActionChiGapSup hp hp1 ψ n ≤ b := by
  apply csSup_le ((show (sourcePeriodicSegment hp hp1 ψ n).Nonempty from
    ⟨_,sourcePeriodicMidpoint_mem_segment hp hp1 ψ n⟩).image _)
  rintro y ⟨z,hz,rfl⟩
  exact hb z hz

/-- The supremum at a collapsed gap is exactly its midpoint error. -/
theorem sourceActionChiGapSup_of_gap_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    sourceActionChiGapSup hp hp1 ψ n =
      ‖sourceActionChi hp hp1 n ψ (sourceStandardRootMidpoint hp hp1 ψ n)-1‖ := by
  have hd : sourceStandardRootHalfGap hp hp1 ψ n = 0 := by
    simp only [sourceStandardRootHalfGap,hg,zero_div]
  simp only [sourceActionChiGapSup,sourcePeriodicSegment_eq_midpoint_segment,hd,
    sub_zero,add_zero,segment_same,image_singleton,csSup_singleton]

/-- At the free source every literal gap supremum is zero. -/
theorem sourceActionChiGapSup_zero_source (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    sourceActionChiGapSup hp hp1 (0 : CoeffPair p) n = 0 := by
  obtain ⟨W,_,_,hr,H⟩ := sourceEquation2_18 hp hp1
  have h0 : (0 : CoeffPair p) ∈ W := hr (by simp [realTypeSourceLocus])
  have hg : canonicalPeriodicGap hp hp1 (periodOnePotential (0 : CoeffPair p))
      (periodOnePotential_mem 0) n = 0 := by
    simpa only [map_zero] using canonicalPeriodicGap_zero hp hp1 n
  rw [sourceActionChiGapSup_of_gap_zero hp hp1 0 n hg,
    sourceActionChi_zero_source hp hp1 n _
      (H.segment_subset_omitted 0 h0 n (sourcePeriodicMidpoint_mem_segment hp hp1 0 n))]
  simp

end NLS.ZakharovShabat
