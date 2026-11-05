import NLS.KdV.HillHminusIntrinsicDeflatedRoot
import NLS.KdV.HillHminusPhysicalPsiZeros
import NLS.KdV.HillHminusFixedPhysicalNumerators
import NLS.KdV.HillDeflatedGapPhysicalMatching

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- Every ORIGINAL normalized Abelian differential has a jointly analytic
deflated H-minus-one chart across EVERY selected gap, including low and
collapsed gaps, with literal physical matching on original L2 neighborhoods. -/
theorem exists_hillOriginal_deflatedDifferential_hminus_gap_chart
    (q : RealPeriodOneHillPotential) (n k : ℕ+) :
    ∃ H : ℂ × PeriodOneHminusOne → ℂ, ∃ E : Set ℂ, ∃ U : Set PeriodOneHminusOne,
      ∃ V : Set RealPeriodOneHillPotential,
      IsOpen E ∧ IsOpen U ∧ IsOpen V ∧
      segment ℝ (hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)-1) : ℂ)
        (hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)) : ℂ) ⊆ E ∧
      hillOriginalHminusSource q.val ∈ U ∧ q ∈ V ∧
      AnalyticOnNhd ℂ H (E ×ˢ U) ∧
      ∀ p ∈ V, hillOriginalHminusSource p.val ∈ U ∧ ∀ z ∈ E,
        z ∈ hillGapFilledDomain p.val p.property.1 p.property.2 k ∧
        H (z,hillOriginalHminusSource p.val) =
          -I*hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n n.pos z /
            hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z := by
  obtain ⟨P,c,_,_,hshift,hqP,hreal,houtside,_⟩ := exists_hillHminusPsiChart_real_form_outside_shift
    (hillOriginalHminusSource q.val) (hillOriginalHminusSource_real q.val q.property.2) 0
  let D := (univ ×ˢ P.source) ∩ hillHminusIntrinsicDeflatedRootDomain q.val q.property.1 q.property.2 k
  have hD : IsOpen D := (isOpen_univ.prod P.source_open).inter
    (isOpen_hillHminusIntrinsicDeflatedRootDomain q.val q.property.1 q.property.2 k k.pos)
  let K := segment ℝ (hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)-1) : ℂ)
    (hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)) : ℂ)
  have hK : IsCompact K := by
    rw [show K = segment ℝ (hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)-1) : ℂ)
      (hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)) : ℂ) from rfl,segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hbase : K ×ˢ {hillOriginalHminusSource q.val} ⊆ D := by
    rintro ⟨z,a⟩ ⟨hz,ha⟩
    rcases mem_singleton_iff.mp ha with rfl
    exact ⟨⟨mem_univ _,hqP⟩,mem_hillHminusIntrinsicDeflatedRootDomain_base
      q.val q.property.1 q.property.2 k k.pos z
      (hillRealGapSegment_subset_intrinsic_contour_ball q.val q.property.1 q.property.2 k k.pos hz)⟩
  obtain ⟨A,U,hA,hU,hKA,hqU,hAU⟩ := generalized_tube_lemma hK isCompact_singleton hD hbase
  obtain ⟨B,W,hB,hW,hKB,hqW,hrootmatch⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching
    q.val q.property.1 q.property.2 k k.pos
  let R : RealPeriodOneHillPotential → PeriodOneHminusOne := fun p => hillOriginalHminusSource p.val
  have hR : Continuous R := hillOriginalHminusSource.continuous.comp continuous_subtype_val
  let V := W ∩ R ⁻¹' U
  let H : ℂ × PeriodOneHminusOne → ℂ := fun t =>
    -I*P.numerator n t/hillHminusIntrinsicDeflatedRoot q.val q.property.1 q.property.2 k t
  have hH : AnalyticOnNhd ℂ H D := by
    intro t ht
    exact (analyticAt_const.mul (P.analytic_numerator n t ht.1)).div
      (analyticOnNhd_hillHminusIntrinsicDeflatedRoot q.val q.property.1 q.property.2 k k.pos t ht.2)
      (hillHminusIntrinsicDeflatedRoot_ne_zero q.val q.property.1 q.property.2 k k.pos t ht.2)
  refine ⟨H,A ∩ B,U,V,hA.inter hB,hU,hW.inter (hU.preimage hR),
    (fun z hz => ⟨hKA hz,hKB hz⟩),hqU (mem_singleton _),⟨hqW,hqU (mem_singleton _)⟩,
    hH.mono (fun t ht => hAU ⟨ht.1.1,ht.2⟩),?_⟩
  intro p hp
  refine ⟨hp.2,?_⟩
  intro z hz
  have hpP : hillOriginalHminusSource p.val ∈ P.source := (hAU (show (z,hillOriginalHminusSource p.val) ∈ A ×ˢ U from ⟨hz.1,hp.2⟩)).1.2
  have hnum := congrFun (P.numerator_eq_original p hpP hreal (houtside _ hpP.1) c hshift n) z
  refine ⟨(hrootmatch p hp.1 z hz.2).2.1,?_⟩
  dsimp only [H]
  rw [hnum,hillHminusIntrinsicDeflatedRoot_original_source q.val q.property.1 q.property.2 k p.val p.property.1,
    (hrootmatch p hp.1 z hz.2).2.2]

end NLS.KdV
