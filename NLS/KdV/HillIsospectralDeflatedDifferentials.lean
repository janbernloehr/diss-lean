import NLS.KdV.HillDeflatedGapPhysicalMatching
import NLS.KdV.HillIsospectralJointDifferentials
import NLS.KdV.HillIsospectralGapUnits
import NLS.ComplexAnalysis.QuotientDerivative

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem exists_hillDeflatedNormalizedDifferential_isospectral_gap_chart
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ H : ℂ × Coeff 2 → ℂ, ∃ E : Set ℂ, ∃ U : Set (Coeff 2),
      ∃ V : Set RealPeriodOneHillPotential,
      IsOpen E ∧ IsOpen U ∧ IsOpen V ∧
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) ⊆ E ∧
      SpectralWeight.one.toCoeff q ∈ U ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ V ∧
      AnalyticOnNhd ℂ H (E ×ˢ U) ∧
      (∀ p ∈ V, SpectralWeight.one.toCoeff p.val ∈ U ∧ ∀ z ∈ E,
        z ∈ hillGapFilledDomain p.val p.property.1 p.property.2 k ∧
        H (z,SpectralWeight.one.toCoeff p.val) =
          -I*hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn z /
            hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z) ∧
      ∀ h : Coeff 2,
        (∀ energy : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b energy) (SpectralWeight.one.toCoeff q)) h=0) →
        ∀ z∈E, (fderiv ℂ (fun b : Coeff 2 => H (z,b)) (SpectralWeight.one.toCoeff q)) h=0 := by
  obtain ⟨G,hG,hGmatch,hGflat⟩ := exists_hillAbelianSelectedGlobalPsi_joint_isospectral_extension q hq hr h0q h0r n hn
  let D := {t | AnalyticAt ℂ G t} ∩ hillLocalDeflatedRootDomain q hq hr k
  have hD : IsOpen D := (isOpen_analyticAt ℂ G).inter (isOpen_hillLocalDeflatedRootDomain q hq hr k hk)
  let K := segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ)
  have hK : IsCompact K := by
    rw [show K = segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ)
      (hillRealLabels q hq hr (2*k) : ℂ) from rfl,segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hbase : K ×ˢ {SpectralWeight.one.toCoeff q} ⊆ D := by
    rintro ⟨z,p⟩ ⟨hz,hp⟩
    have he : p = SpectralWeight.one.toCoeff q := hp
    subst p
    exact ⟨hG z,mem_hillLocalDeflatedRootDomain_base q hq hr k hk z
      (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk hz)⟩
  obtain ⟨A,U,hA,hU,hKA,hqU,hAU⟩ := generalized_tube_lemma hK isCompact_singleton hD hbase
  obtain ⟨B,W,hB,hW,hKB,hqW,hrootmatch⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching q hq hr k hk
  obtain ⟨T,hTsub,hT,hqT⟩ := _root_.mem_nhds_iff.mp hGmatch
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let V := (W ∩ T) ∩ P ⁻¹' U
  let H : ℂ × Coeff 2 → ℂ := fun t => -I*G t/hillLocalDeflatedComplexRoot q hq hr k t
  have hH : AnalyticOnNhd ℂ H D := by
    intro t ht
    exact (analyticAt_const.mul ht.1).div
      (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk t ht.2)
      (hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk t ht.2)
  refine ⟨H,A ∩ B,U,V,hA.inter hB,hU,(hW.inter hT).inter (hU.preimage hP),
    fun z hz => ⟨hKA hz,hKB hz⟩,hqU (mem_singleton _),⟨⟨hqW,hqT⟩,hqU (mem_singleton _)⟩,
    hH.mono (fun t ht => hAU ⟨ht.1.1,ht.2⟩),?_,?_⟩
  · intro p hp
    refine ⟨hp.2,?_⟩
    intro z hz
    refine ⟨(hrootmatch p hp.1.1 z hz.2).2.1,?_⟩
    change -I*G (z,SpectralWeight.one.toCoeff p.val)/_ = _
    rw [hTsub hp.1.2 z,(hrootmatch p hp.1.1 z hz.2).2.2]
  · intro h hiso z hz
    have hdom := hAU (show (z,SpectralWeight.one.toCoeff q)∈A ×ˢ U from ⟨hz.1,hqU (mem_singleton _)⟩)
    have hn : AnalyticAt ℂ (fun b : Coeff 2 => G (z,b)) (SpectralWeight.one.toCoeff q) :=
      (hG z).comp (f := fun b : Coeff 2 => (z,b)) (analyticAt_const.prod analyticAt_id)
    have hd : AnalyticAt ℂ (fun b : Coeff 2 => hillLocalDeflatedComplexRoot q hq hr k (z,b))
        (SpectralWeight.one.toCoeff q) :=
      (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk _ hdom.2).comp
        (f := fun b : Coeff 2 => (z,b)) (analyticAt_const.prod analyticAt_id)
    have hne := hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk _ hdom.2
    have hnc : AnalyticAt ℂ (fun b : Coeff 2 => -I*G (z,b)) (SpectralWeight.one.toCoeff q) :=
      analyticAt_const.mul hn
    have hnc0 : (fderiv ℂ (fun b : Coeff 2 => -I*G (z,b)) (SpectralWeight.one.toCoeff q)) h=0 := by
      rw [fderiv_const_mul hn.differentiableAt]
      simp only [smul_apply,smul_eq_mul,hGflat h hiso z,mul_zero]
    change (fderiv ℂ (fun b : Coeff 2 => (-I*G (z,b))/hillLocalDeflatedComplexRoot q hq hr k (z,b))
      (SpectralWeight.one.toCoeff q)) h=0
    rw [fderiv_div_apply _ _ _ hnc.differentiableAt hd.differentiableAt hne h,hnc0,
      hillLocalDeflatedComplexRoot_isospectral_fderiv q hq hr k hk h hiso z hdom.2.1.2.1]
    simp only [zero_mul,mul_zero,sub_zero,zero_div]

end NLS.KdV
