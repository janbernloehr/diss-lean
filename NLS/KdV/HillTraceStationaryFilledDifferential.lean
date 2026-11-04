import NLS.KdV.HillGardnerFilledDifferential
import NLS.KdV.HillTraceStationaryDeflatedRoot
import NLS.KdV.HillTraceStationaryCanonicalDifferential

/-! # Actual filled-gap normalized differential charts along trace-stationary tangents -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
  (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
  (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The genuine normalized deflated differential admits a stationary jointly
analytic chart across the whole closed gap, including its endpoints. -/
theorem exists_hillDeflatedNormalizedDifferential_trace_stationary_analytic_gap_chart
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) :
    ∃ H : ℂ × Coeff 2 → ℂ, ∃ E : Set ℂ, ∃ U : Set (Coeff 2), ∃ V : Set RealPeriodOneHillPotential,
      IsOpen E ∧ IsOpen U ∧ IsOpen V ∧
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) ⊆ E ∧
      SpectralWeight.one.toCoeff q∈U ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      AnalyticOnNhd ℂ H (E ×ˢ U) ∧
      (∀ z∈E, ∀ V : Coeff 2, (∀ z : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) (SpectralWeight.one.toCoeff q)) V=0) → (fderiv ℂ (fun p : Coeff 2 => H (z,p)) (SpectralWeight.one.toCoeff q))
        (V)=0) ∧
      ∀ p∈V, SpectralWeight.one.toCoeff p.val∈U ∧ ∀ z∈E,
        z∈hillGapFilledDomain p.val p.property.1 p.property.2 k ∧
        H (z,SpectralWeight.one.toCoeff p.val)=
          -I*hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn z/
            hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z := by
  obtain ⟨G,hG,hGzero,hGmatch⟩ :=
    exists_hillAbelianSelectedGlobalPsi_trace_stationary_joint_analytic_extension q hq hr h0q h0r n hn
  let D := {t | AnalyticAt ℂ G t} ∩ hillLocalDeflatedRootDomain q hq hr k
  have hD : IsOpen D := (isOpen_analyticAt ℂ G).inter (isOpen_hillLocalDeflatedRootDomain q hq hr k hk)
  let K := segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ)
  have hK : IsCompact K := by
    rw [show K=segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) from rfl,
      segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hbase : K ×ˢ {SpectralWeight.one.toCoeff q} ⊆ D := by
    rintro ⟨z,p⟩ ⟨hz,hp⟩
    have he : p=SpectralWeight.one.toCoeff q := hp
    subst p
    exact ⟨hG z,mem_hillLocalDeflatedRootDomain_base q hq hr k hk z
      (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk hz)⟩
  obtain ⟨A,U,hA,hU,hKA,hqU,hAU⟩ := generalized_tube_lemma hK isCompact_singleton hD hbase
  obtain ⟨B,W,hB,hW,hKB,hqW,hrootmatch⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching q hq hr k hk
  obtain ⟨T,hTsub,hT,hqT⟩ := _root_.mem_nhds_iff.mp hGmatch
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let V := (W ∩ T) ∩ P ⁻¹' U
  let H (t : ℂ × Coeff 2) := -I*G t/hillLocalDeflatedComplexRoot q hq hr k t
  have hH : AnalyticOnNhd ℂ H D := by
    intro t ht
    exact (analyticAt_const.mul ht.1).div
      (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk t ht.2)
      (hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk t ht.2)
  let C := ball (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)
  refine ⟨H,(A ∩ B) ∩ C,U,V,(hA.inter hB).inter isOpen_ball,hU,(hW.inter hT).inter (hU.preimage hP),
    (fun z hz => ⟨⟨hKA hz,hKB hz⟩,hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk hz⟩),
    hqU (mem_singleton _),⟨⟨hqW,hqT⟩,hqU (mem_singleton _)⟩,
    hH.mono (fun t ht => hAU ⟨ht.1.1.1,ht.2⟩),?_,?_⟩
  · intro z hz V hV
    have hd := mem_hillLocalDeflatedRootDomain_base q hq hr k hk z hz.2
    have hN : AnalyticAt ℂ (fun p : Coeff 2 => -I*G (z,p)) (SpectralWeight.one.toCoeff q) :=
      analyticAt_const.mul ((hG z).comp (f := fun p : Coeff 2 => (z,p)) (analyticAt_const.prod analyticAt_id))
    have hR := (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk _ hd).comp
      (f := fun p : Coeff 2 => (z,p)) (analyticAt_const.prod analyticAt_id)
    have hzN : (fderiv ℂ (fun p : Coeff 2 => -I*G (z,p)) (SpectralWeight.one.toCoeff q))
        (V)=0 := by
      change (fderiv ℂ ((-I : ℂ) • fun p : Coeff 2 => G (z,p)) _) _=0
      rw [fderiv_const_smul_field]
      change -I*((fderiv ℂ (fun p : Coeff 2 => G (z,p)) _) _)=0
      rw [hGzero V hV z,mul_zero]
    change (fderiv ℂ (fun p : Coeff 2 => -I*G (z,p)/hillLocalDeflatedComplexRoot q hq hr k (z,p)) _) _=0
    rw [fderiv_div_apply (fun p : Coeff 2 => -I*G (z,p))
      (fun p : Coeff 2 => hillLocalDeflatedComplexRoot q hq hr k (z,p)) _ hN.differentiableAt hR.differentiableAt
      (hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk _ hd),hzN,
      fderiv_hillLocalDeflatedComplexRoot_of_trace_stationary q hq hr k hk z V hV hz.2]
    simp
  · intro p hp
    refine ⟨hp.2,?_⟩
    intro z hz
    refine ⟨(hrootmatch p hp.1.1 z hz.1.2).2.1,?_⟩
    change -I*G (z,SpectralWeight.one.toCoeff p.val)/_= _
    rw [hTsub hp.1.2 z,(hrootmatch p hp.1.1 z hz.1.2).2.2]

end NLS.KdV
