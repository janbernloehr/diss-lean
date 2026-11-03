import NLS.KdV.HillLocalGapUnitPhysical

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillLocalDeflatedRootRatio (k : ℕ) (t : ℂ × Coeff 2) : ℂ :=
  hillLocalGapUnit q hq hr k t / hillDeflatedEnergyCanonicalRoot q hq hr k t.1 ^ 2

def hillLocalDeflatedRootPreDomain (k : ℕ) : Set (ℂ × Coeff 2) :=
  {t | AnalyticAt ℂ (hillLocalGapUnit q hq hr k) t} ∩
    (ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) ×ˢ univ)

def hillLocalDeflatedRootDomain (k : ℕ) : Set (ℂ × Coeff 2) :=
  hillLocalDeflatedRootPreDomain q hq hr k ∩ (hillLocalDeflatedRootRatio q hq hr k) ⁻¹' slitPlane

def hillLocalDeflatedComplexRoot (k : ℕ) (t : ℂ × Coeff 2) : ℂ :=
  hillDeflatedEnergyCanonicalRoot q hq hr k t.1 * sqrt (hillLocalDeflatedRootRatio q hq hr k t)

theorem analyticOnNhd_hillLocalDeflatedRootRatio (k : ℕ) (hk : 1 ≤ k) :
    AnalyticOnNhd ℂ (hillLocalDeflatedRootRatio q hq hr k) (hillLocalDeflatedRootPreDomain q hq hr k) := by
  intro t ht
  have hfilled := hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk
    (ball_subset_closedBall ht.2.1)
  have hB : AnalyticAt ℂ (fun s : ℂ × Coeff 2 => hillDeflatedEnergyCanonicalRoot q hq hr k s.1) t :=
    (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k t.1 hfilled).comp analyticAt_fst
  exact ht.1.div (hB.pow 2) (pow_ne_zero 2 (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk t.1 hfilled))

theorem isOpen_hillLocalDeflatedRootPreDomain (k : ℕ) :
    IsOpen (hillLocalDeflatedRootPreDomain q hq hr k) :=
  (isOpen_analyticAt ℂ (hillLocalGapUnit q hq hr k)).inter (isOpen_ball.prod isOpen_univ)

theorem isOpen_hillLocalDeflatedRootDomain (k : ℕ) (hk : 1 ≤ k) :
    IsOpen (hillLocalDeflatedRootDomain q hq hr k) :=
  (analyticOnNhd_hillLocalDeflatedRootRatio q hq hr k hk).continuousOn.isOpen_inter_preimage
    (isOpen_hillLocalDeflatedRootPreDomain q hq hr k) isOpen_slitPlane

theorem hillLocalGapUnit_at_base (k : ℕ) (hk : 1 ≤ k) (z : ℂ)
    (hz : z ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    hillLocalGapUnit q hq hr k (z,SpectralWeight.one.toCoeff q) =
      hillDeflatedEnergyCanonicalRoot q hq hr k z^2 :=
  hillLocalGapUnit_eq_physical_of_geometry q hq hr q hq hr k hk
    (hillRealGapContour_band_bounds q hq hr k hk)
    (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk) hz

theorem mem_hillLocalDeflatedRootDomain_base (k : ℕ) (hk : 1 ≤ k) (z : ℂ)
    (hz : z ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    (z,SpectralWeight.one.toCoeff q) ∈ hillLocalDeflatedRootDomain q hq hr k := by
  obtain ⟨V,_,hqV,hU⟩ := exists_hillLocalGapUnit_analytic_neighborhood q hq hr k hk
  refine ⟨⟨hU (z,SpectralWeight.one.toCoeff q) ⟨hz,hqV⟩,hz,mem_univ _⟩,?_⟩
  change hillLocalGapUnit q hq hr k (z,SpectralWeight.one.toCoeff q)/
    hillDeflatedEnergyCanonicalRoot q hq hr k z^2 ∈ slitPlane
  rw [hillLocalGapUnit_at_base q hq hr k hk z hz,
    div_self (pow_ne_zero 2 (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk z
      (hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk (ball_subset_closedBall hz))))]
  exact one_mem_slitPlane

theorem analyticOnNhd_hillLocalDeflatedComplexRoot (k : ℕ) (hk : 1 ≤ k) :
    AnalyticOnNhd ℂ (hillLocalDeflatedComplexRoot q hq hr k) (hillLocalDeflatedRootDomain q hq hr k) := by
  intro t ht
  have hfilled := hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk
    (ball_subset_closedBall ht.1.2.1)
  have hB : AnalyticAt ℂ (fun s : ℂ × Coeff 2 => hillDeflatedEnergyCanonicalRoot q hq hr k s.1) t :=
    (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k t.1 hfilled).comp analyticAt_fst
  have hs := Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds ht.2)
  exact hB.mul (hs.comp (analyticOnNhd_hillLocalDeflatedRootRatio q hq hr k hk t ht.1))

theorem hillLocalDeflatedComplexRoot_base (k : ℕ) (hk : 1 ≤ k) (z : ℂ)
    (hz : z ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    hillLocalDeflatedComplexRoot q hq hr k (z,SpectralWeight.one.toCoeff q) =
      hillDeflatedEnergyCanonicalRoot q hq hr k z := by
  unfold hillLocalDeflatedComplexRoot hillLocalDeflatedRootRatio
  rw [hillLocalGapUnit_at_base q hq hr k hk z hz,
    div_self (pow_ne_zero 2 (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk z
      (hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk (ball_subset_closedBall hz))))]
  simp only [sqrt_one,mul_one]

theorem hillLocalDeflatedComplexRoot_sq (k : ℕ) (hk : 1 ≤ k) (t : ℂ × Coeff 2)
    (ht : t ∈ hillLocalDeflatedRootDomain q hq hr k) :
    hillLocalDeflatedComplexRoot q hq hr k t^2 = hillLocalGapUnit q hq hr k t := by
  have hB := hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk t.1
    (hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk (ball_subset_closedBall ht.1.2.1))
  have hs : (sqrt (hillLocalDeflatedRootRatio q hq hr k t))^2 = hillLocalDeflatedRootRatio q hq hr k t := by
    have h := Complex.cpow_nat_inv_pow (hillLocalDeflatedRootRatio q hq hr k t) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [sqrt,one_div] using h
  rw [hillLocalDeflatedComplexRoot,mul_pow,hs,hillLocalDeflatedRootRatio]
  exact mul_div_cancel₀ _ (pow_ne_zero 2 hB)

theorem hillLocalDeflatedComplexRoot_ne_zero (k : ℕ) (hk : 1 ≤ k) (t : ℂ × Coeff 2)
    (ht : t ∈ hillLocalDeflatedRootDomain q hq hr k) :
    hillLocalDeflatedComplexRoot q hq hr k t ≠ 0 := by
  intro hzero
  have hu := hillLocalDeflatedComplexRoot_sq q hq hr k hk t ht
  rw [hzero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hu
  have hratio : hillLocalDeflatedRootRatio q hq hr k t = 0 := by
    rw [hillLocalDeflatedRootRatio,← hu,zero_div]
  exact zero_notMem_slitPlane (hratio ▸ ht.2)

theorem exists_hillLocalDeflatedRoot_gap_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ E : Set ℂ, ∃ V : Set (Coeff 2), IsOpen E ∧ IsOpen V ∧
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) ⊆ E ∧
      SpectralWeight.one.toCoeff q ∈ V ∧ E ×ˢ V ⊆ hillLocalDeflatedRootDomain q hq hr k := by
  let K := segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ)
  have hK : IsCompact K := by
    rw [show K = segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ)
      (hillRealLabels q hq hr (2*k) : ℂ) from rfl,segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hbase : K ×ˢ {SpectralWeight.one.toCoeff q} ⊆ hillLocalDeflatedRootDomain q hq hr k := by
    rintro ⟨z,p⟩ ⟨hz,hp⟩
    have he : p = SpectralWeight.one.toCoeff q := hp
    subst p
    exact mem_hillLocalDeflatedRootDomain_base q hq hr k hk z
      (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk hz)
  obtain ⟨E,V,hE,hV,hKE,hqV,hEV⟩ := generalized_tube_lemma hK isCompact_singleton
    (isOpen_hillLocalDeflatedRootDomain q hq hr k hk) hbase
  exact ⟨E,V,hE,hV,hKE,hqV (mem_singleton _),hEV⟩

end NLS.KdV
