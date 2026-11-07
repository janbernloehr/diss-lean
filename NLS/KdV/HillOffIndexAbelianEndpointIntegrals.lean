import NLS.KdV.HillAbelianCollapsedGapExtension
import NLS.ComplexAnalysis.PolygonalEndpointIntegral
import NLS.ComplexAnalysis.PrimitiveRemovableBoundary
import NLS.ComplexAnalysis.PrimitiveBoundaryPathIntegral

/-! The endpoint-normalized off-index primitive equals a GENUINE
improper limit of finite polygonal path integrals. Endpoint limits
are nonvacuous, normalization is unique, and integrable connectors
between the two gap ends have zero integral. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def offIndexAbelianEndpointIntegral (P : HillProductEquationPatch) (n m : ℕ+)
    (q : PeriodOneHminusOne) (ν : ℂ) : ℂ :=
  endpointPolygonalIntegral (fun z => P.abelianFrequencyDifferential n (z,q)) (P.abelianGapDisc m q)
    (canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ)) ν

theorem abelianGapDisc_open (P : HillProductEquationPatch) (m : ℕ+) (q : PeriodOneHminusOne) :
    IsOpen (P.abelianGapDisc m q) := by
  apply isOpen_ball.sdiff
  apply IsCompact.isClosed
  change IsCompact (segment ℝ _ _)
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem abelianGapDisc_connected (P : HillProductEquationPatch) (m : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) : IsConnected (P.abelianGapDisc m q) := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  exact (isPathConnected_convex_complex_segment_complement_including_singleton _ _ _ isOpen_ball
    (convex_ball _ _) (D.gap (left_mem_segment ℝ _ _))).isConnected

theorem abelianGap_leftEndpoint_mem_closure (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ) ∈
      closure (P.abelianGapDisc m q) := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  exact (dense_complex_segment_complement _ _).open_subset_closure_inter isOpen_ball (D.gap (left_mem_segment ℝ _ _))

theorem offIndexAbelianEndpointIntegral_eq_normalized_primitive (P : HillProductEquationPatch)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (F : ℂ → ℂ)
    (hF : ∀ z ∈ P.abelianGapDisc m q, HasDerivAt F (P.abelianFrequencyDifferential n (z,q)) z)
    (hleft : Tendsto F (𝓝[P.abelianGapDisc m q] (canonicalPeriodicLeft (by norm_num) (by norm_num)
      (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 0))
    (ν : ℂ) (hν : ν ∈ P.abelianGapDisc m q) : P.offIndexAbelianEndpointIntegral n m q ν = F ν := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hf : ContinuousOn (fun z => P.abelianFrequencyDifferential n (z,q)) (P.abelianGapDisc m q) := by
    intro z hz
    exact (P.analytic_abelianFrequencyDifferential_on_closed_cut_disc n m q hq D z
      ⟨ball_subset_closedBall hz.1,hz.2⟩).continuousAt.continuousWithinAt
  have he := endpointPolygonalIntegral_eq_sub _ F _ (P.abelianGapDisc_open m q)
    (P.abelianGapDisc_connected m q hq).isPreconnected hf hF _ ν 0
    (P.abelianGap_leftEndpoint_mem_closure m q hq) hν hleft
  simpa only [offIndexAbelianEndpointIntegral,sub_zero] using he

theorem offIndexAbelian_normalized_primitive_unique (P : HillProductEquationPatch)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (F G : ℂ → ℂ)
    (hF : ∀ z ∈ P.abelianGapDisc m q, HasDerivAt F (P.abelianFrequencyDifferential n (z,q)) z)
    (hG : ∀ z ∈ P.abelianGapDisc m q, HasDerivAt G (P.abelianFrequencyDifferential n (z,q)) z)
    (hleftF : Tendsto F (𝓝[P.abelianGapDisc m q] (canonicalPeriodicLeft (by norm_num) (by norm_num)
      (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 0))
    (hleftG : Tendsto G (𝓝[P.abelianGapDisc m q] (canonicalPeriodicLeft (by norm_num) (by norm_num)
      (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 0)) :
    EqOn F G (P.abelianGapDisc m q) := by
  let : NeBot (𝓝[P.abelianGapDisc m q] (canonicalPeriodicLeft (by norm_num) (by norm_num)
      (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) :=
    mem_closure_iff_nhdsWithin_neBot.mp (P.abelianGap_leftEndpoint_mem_closure m q hq)
  exact primitives_eq_of_common_boundary_limit _ F G _ _ 0 (P.abelianGapDisc_open m q)
    (P.abelianGapDisc_connected m q hq).isPreconnected hF hG hleftF hleftG

end NLS.KdV.HillProductEquationPatch
