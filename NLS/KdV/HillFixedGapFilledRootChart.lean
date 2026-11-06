import NLS.KdV.HillDeflatedGapPhysicalMatching
import NLS.KdV.HillFilledFreeGapRoot
import NLS.ComplexAnalysis.CompactParameterBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Each fixed free gap has a common local complex deflated-root chart
and inverse bound with exact original real physical matching. -/
theorem exists_hillFixedGap_filled_root_local_chart (k : ℕ) (hk : 1≤k) :
    ∃ r δ C : ℝ, 0<r ∧ 0<δ ∧ 0<C ∧
      r≤(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/2 ∧
      AnalyticOnNhd ℂ (hillFilledFreeGapRoot h0q h0r k)
        (closedBall (hillRealGapCenter 0 h0q h0r k : ℂ) r ×ˢ ball 0 δ) ∧
      (∀ p∈ball 0 δ, ∀ E∈closedBall (hillRealGapCenter 0 h0q h0r k : ℂ) r,
        hillFilledFreeGapRoot h0q h0r k (E,p)≠0 ∧ ‖(hillFilledFreeGapRoot h0q h0r k (E,p))⁻¹‖≤C) ∧
      ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ →
        ∀ E∈closedBall (hillRealGapCenter 0 h0q h0r k : ℂ) r,
        hillFilledFreeGapRoot h0q h0r k (E,SpectralWeight.one.toCoeff q.val)=
          hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k E := by
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let q0 : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  obtain ⟨E,Vr,hE,hVr,hgapE,h0Vr,hphysical⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching 0 h0q h0r k hk
  have hcE : c∈E := by
    have hh := hgapE (left_mem_segment ℝ _ _)
    rw [(hillFreeGapEndpoints h0q h0r k hk).1] at hh
    simpa only [c,hillFreeGapCenter h0q h0r k hk] using hh
  let D := hillLocalDeflatedRootDomain 0 h0q h0r k ∩ ((E∩ball c R) ×ˢ univ)
  have hD : IsOpen D := (isOpen_hillLocalDeflatedRootDomain 0 h0q h0r k hk).inter
    ((hE.inter isOpen_ball).prod isOpen_univ)
  have hcD : (c,(0 : Coeff 2))∈D := by
    refine ⟨?_,⟨hcE,mem_ball_self hR⟩,mem_univ _⟩
    simpa only [map_zero] using mem_hillLocalDeflatedRootDomain_base 0 h0q h0r k hk c (mem_ball_self hR)
  obtain ⟨A,U,hA,hU,hcA,h0U,hAU⟩ := isOpen_prod_iff.mp hD c 0 hcD
  obtain ⟨a,ha,haA⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds hcA)
  let r := min (a/2) (R/4)
  have hr : 0<r := by dsimp only [r];positivity
  have hra : r<a := (min_le_left _ _).trans_lt (by linarith)
  have hK (z : ℂ) (hz : z∈closedBall c r) : (z,(0 : Coeff 2))∈D :=
    hAU ⟨haA (closedBall_subset_ball hra hz),h0U⟩
  have hi : ContinuousOn (fun t : ℂ × Coeff 2 => (hillLocalDeflatedComplexRoot 0 h0q h0r k t)⁻¹) D := by
    intro t ht
    exact (((analyticOnNhd_hillLocalDeflatedComplexRoot 0 h0q h0r k hk t ht.1).inv
      (hillLocalDeflatedComplexRoot_ne_zero 0 h0q h0r k hk t ht.1)).continuousAt).continuousWithinAt
  obtain ⟨V,hV,h0V,C,hC,hbound⟩ := exists_local_uniform_bound_on_compact_of_continuousOn
    (fun t : ℂ × Coeff 2 => (hillLocalDeflatedComplexRoot 0 h0q h0r k t)⁻¹) D hD hi
    (closedBall c r) (isCompact_closedBall c r) (0 : Coeff 2) hK
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  obtain ⟨εr,hεr,hεrV⟩ := Metric.mem_nhds_iff.mp (hVr.mem_nhds h0Vr)
  let δ := min ε εr
  have hδ : 0<δ := lt_min hε hεr
  have hpV (p : Coeff 2) (hp : p∈ball 0 δ) : p∈V :=
    hεV (ball_subset_ball (min_le_left _ _) hp)
  refine ⟨r,δ,C+1,hr,hδ,by positivity,?_,?_,?_,?_⟩
  · have hh : r≤R/4 := min_le_right _ _
    linarith
  · intro t ht
    have hd := (hbound t.2 (hpV t.2 ht.2) t.1 ht.1).1
    apply (analyticOnNhd_hillLocalDeflatedComplexRoot 0 h0q h0r k hk t hd.1).congr
    filter_upwards [(isOpen_ball.prod isOpen_univ).mem_nhds
      (show t∈ball c R ×ˢ univ from ⟨hd.2.1.2,mem_univ _⟩)] with u hu
    exact (hillFilledFreeGapRoot_eq_local h0q h0r k u.2 u.1 hu.1).symm
  · intro p hp z hz
    have hd := (hbound p (hpV p hp) z hz).1
    rw [hillFilledFreeGapRoot_eq_local h0q h0r k p z hd.2.1.2]
    exact ⟨hillLocalDeflatedComplexRoot_ne_zero 0 h0q h0r k hk (z,p) hd.1,
      (hbound p (hpV p hp) z hz).2.trans (by linarith)⟩
  · intro q hq z hz
    have hqV : q∈Vr := by
      apply hεrV
      rw [mem_ball]
      change dist q.val (0 : WeightedCoeff SpectralWeight.one.toWeight 2)<εr
      rw [dist_zero_right]
      exact hq.trans_le (min_le_right _ _)
    have hp : SpectralWeight.one.toCoeff q.val∈ball 0 δ := by
      rw [mem_ball,dist_zero_right]
      exact (SpectralWeight.one.norm_toCoeff_le q.val).trans_lt hq
    have hd := (hbound _ (hpV _ hp) z hz).1
    rw [hillFilledFreeGapRoot_eq_local h0q h0r k _ z hd.2.1.2]
    exact (hphysical q hqV z hd.2.1.1).2.2

end NLS.KdV
