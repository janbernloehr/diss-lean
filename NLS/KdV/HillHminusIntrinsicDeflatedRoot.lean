import NLS.KdV.HillHminusIntrinsicGapUnit
import NLS.KdV.HillLocalDeflatedComplexRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillHminusIntrinsicDeflatedRootRatio (k : ℕ) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillHminusIntrinsicGapUnit q hq hr k t / hillDeflatedEnergyCanonicalRoot q hq hr k t.1 ^ 2

def hillHminusIntrinsicDeflatedRootPreDomain (k : ℕ) : Set (ℂ × PeriodOneHminusOne) :=
  {t | AnalyticAt ℂ (hillHminusIntrinsicGapUnit q hq hr k) t} ∩
    (ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) ×ˢ univ)

def hillHminusIntrinsicDeflatedRootDomain (k : ℕ) : Set (ℂ × PeriodOneHminusOne) :=
  hillHminusIntrinsicDeflatedRootPreDomain q hq hr k ∩ (hillHminusIntrinsicDeflatedRootRatio q hq hr k) ⁻¹' slitPlane

def hillHminusIntrinsicDeflatedRoot (k : ℕ) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillDeflatedEnergyCanonicalRoot q hq hr k t.1 * sqrt (hillHminusIntrinsicDeflatedRootRatio q hq hr k t)

theorem analyticOnNhd_hillHminusIntrinsicDeflatedRootRatio (k : ℕ) (hk : 1 ≤ k) :
    AnalyticOnNhd ℂ (hillHminusIntrinsicDeflatedRootRatio q hq hr k) (hillHminusIntrinsicDeflatedRootPreDomain q hq hr k) := by
  intro t ht
  have hfilled := hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk
    (ball_subset_closedBall ht.2.1)
  have hB : AnalyticAt ℂ (fun s : ℂ × PeriodOneHminusOne => hillDeflatedEnergyCanonicalRoot q hq hr k s.1) t :=
    (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k t.1 hfilled).comp analyticAt_fst
  exact ht.1.div (hB.pow 2) (pow_ne_zero 2 (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk t.1 hfilled))

theorem isOpen_hillHminusIntrinsicDeflatedRootPreDomain (k : ℕ) :
    IsOpen (hillHminusIntrinsicDeflatedRootPreDomain q hq hr k) :=
  (isOpen_analyticAt ℂ (hillHminusIntrinsicGapUnit q hq hr k)).inter (isOpen_ball.prod isOpen_univ)

theorem isOpen_hillHminusIntrinsicDeflatedRootDomain (k : ℕ) (hk : 1 ≤ k) :
    IsOpen (hillHminusIntrinsicDeflatedRootDomain q hq hr k) :=
  (analyticOnNhd_hillHminusIntrinsicDeflatedRootRatio q hq hr k hk).continuousOn.isOpen_inter_preimage
    (isOpen_hillHminusIntrinsicDeflatedRootPreDomain q hq hr k) isOpen_slitPlane

theorem hillHminusIntrinsicGapUnit_at_base (k : ℕ) (hk : 1 ≤ k) (z : ℂ)
    (hz : z ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    hillHminusIntrinsicGapUnit q hq hr k (z,hillOriginalHminusSource q) =
      hillDeflatedEnergyCanonicalRoot q hq hr k z^2 :=
  by
    rw [hillHminusIntrinsicGapUnit_original_source q hq hr k q hq]
    exact hillLocalGapUnit_at_base q hq hr k hk z hz

theorem mem_hillHminusIntrinsicDeflatedRootDomain_base (k : ℕ) (hk : 1 ≤ k) (z : ℂ)
    (hz : z ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    (z,hillOriginalHminusSource q) ∈ hillHminusIntrinsicDeflatedRootDomain q hq hr k := by
  obtain ⟨V,_,hqV,hU⟩ := exists_hillHminusIntrinsicGapUnit_analytic_neighborhood q hq hr k hk
  refine ⟨⟨hU (z,hillOriginalHminusSource q) ⟨hz,hqV⟩,hz,mem_univ _⟩,?_⟩
  change hillHminusIntrinsicGapUnit q hq hr k (z,hillOriginalHminusSource q)/
    hillDeflatedEnergyCanonicalRoot q hq hr k z^2 ∈ slitPlane
  rw [hillHminusIntrinsicGapUnit_at_base q hq hr k hk z hz,
    div_self (pow_ne_zero 2 (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk z
      (hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk (ball_subset_closedBall hz))))]
  exact one_mem_slitPlane

theorem analyticOnNhd_hillHminusIntrinsicDeflatedRoot (k : ℕ) (hk : 1 ≤ k) :
    AnalyticOnNhd ℂ (hillHminusIntrinsicDeflatedRoot q hq hr k) (hillHminusIntrinsicDeflatedRootDomain q hq hr k) := by
  intro t ht
  have hfilled := hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk
    (ball_subset_closedBall ht.1.2.1)
  have hB : AnalyticAt ℂ (fun s : ℂ × PeriodOneHminusOne => hillDeflatedEnergyCanonicalRoot q hq hr k s.1) t :=
    (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k t.1 hfilled).comp analyticAt_fst
  have hs := Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds ht.2)
  exact hB.mul (hs.comp (analyticOnNhd_hillHminusIntrinsicDeflatedRootRatio q hq hr k hk t ht.1))

theorem hillHminusIntrinsicDeflatedRoot_base (k : ℕ) (hk : 1 ≤ k) (z : ℂ)
    (hz : z ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    hillHminusIntrinsicDeflatedRoot q hq hr k (z,hillOriginalHminusSource q) =
      hillDeflatedEnergyCanonicalRoot q hq hr k z := by
  unfold hillHminusIntrinsicDeflatedRoot hillHminusIntrinsicDeflatedRootRatio
  rw [hillHminusIntrinsicGapUnit_at_base q hq hr k hk z hz,
    div_self (pow_ne_zero 2 (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk z
      (hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk (ball_subset_closedBall hz))))]
  simp only [sqrt_one,mul_one]

theorem hillHminusIntrinsicDeflatedRoot_sq (k : ℕ) (hk : 1 ≤ k) (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ hillHminusIntrinsicDeflatedRootDomain q hq hr k) :
    hillHminusIntrinsicDeflatedRoot q hq hr k t^2 = hillHminusIntrinsicGapUnit q hq hr k t := by
  have hB := hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk t.1
    (hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk (ball_subset_closedBall ht.1.2.1))
  have hs : (sqrt (hillHminusIntrinsicDeflatedRootRatio q hq hr k t))^2 = hillHminusIntrinsicDeflatedRootRatio q hq hr k t := by
    have h := Complex.cpow_nat_inv_pow (hillHminusIntrinsicDeflatedRootRatio q hq hr k t) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [sqrt,one_div] using h
  rw [hillHminusIntrinsicDeflatedRoot,mul_pow,hs,hillHminusIntrinsicDeflatedRootRatio]
  exact mul_div_cancel₀ _ (pow_ne_zero 2 hB)

theorem hillHminusIntrinsicDeflatedRoot_ne_zero (k : ℕ) (hk : 1 ≤ k) (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ hillHminusIntrinsicDeflatedRootDomain q hq hr k) :
    hillHminusIntrinsicDeflatedRoot q hq hr k t ≠ 0 := by
  intro hzero
  have hu := hillHminusIntrinsicDeflatedRoot_sq q hq hr k hk t ht
  rw [hzero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hu
  have hratio : hillHminusIntrinsicDeflatedRootRatio q hq hr k t = 0 := by
    rw [hillHminusIntrinsicDeflatedRootRatio,← hu,zero_div]
  exact zero_notMem_slitPlane (hratio ▸ ht.2)

theorem exists_hillHminusIntrinsicDeflatedRoot_gap_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ E : Set ℂ, ∃ V : Set (PeriodOneHminusOne), IsOpen E ∧ IsOpen V ∧
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) ⊆ E ∧
      hillOriginalHminusSource q ∈ V ∧ E ×ˢ V ⊆ hillHminusIntrinsicDeflatedRootDomain q hq hr k := by
  let K := segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ)
  have hK : IsCompact K := by
    rw [show K = segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ)
      (hillRealLabels q hq hr (2*k) : ℂ) from rfl,segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hbase : K ×ˢ {hillOriginalHminusSource q} ⊆ hillHminusIntrinsicDeflatedRootDomain q hq hr k := by
    rintro ⟨z,p⟩ ⟨hz,hp⟩
    have he : p = hillOriginalHminusSource q := hp
    subst p
    exact mem_hillHminusIntrinsicDeflatedRootDomain_base q hq hr k hk z
      (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk hz)
  obtain ⟨E,V,hE,hV,hKE,hqV,hEV⟩ := generalized_tube_lemma hK isCompact_singleton
    (isOpen_hillHminusIntrinsicDeflatedRootDomain q hq hr k hk) hbase
  exact ⟨E,V,hE,hV,hKE,hqV (mem_singleton _),hEV⟩

/-- The relative deflated root retains the EXACT original sign and
value on every original even source; no source-neighborhood condition is
needed for this identity of the actual defining functions. -/
theorem hillHminusIntrinsicDeflatedRoot_original_source (k : ℕ)
    (p : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hp : SpectralWeight.one.toCoeff p ∈ Coeff.paritySubspace 0) (z : ℂ) :
    hillHminusIntrinsicDeflatedRoot q hq hr k (z,hillOriginalHminusSource p) =
      hillLocalDeflatedComplexRoot q hq hr k (z,SpectralWeight.one.toCoeff p) := by
  rw [hillHminusIntrinsicDeflatedRoot,hillLocalDeflatedComplexRoot,
    hillHminusIntrinsicDeflatedRootRatio,hillLocalDeflatedRootRatio,
    hillHminusIntrinsicGapUnit_original_source q hq hr k p hp]

end NLS.KdV
