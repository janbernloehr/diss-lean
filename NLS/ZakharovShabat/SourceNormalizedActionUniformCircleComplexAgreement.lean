import NLS.ZakharovShabat.SourceDistantActionFreeCircleCharts
import NLS.ZakharovShabat.SourceDistantNormalizedActionCircleCandidateAnalytic
import NLS.ZakharovShabat.SourceNormalizedActionCollapsedCircleValue

/-!
# Uniform complex agreement of distant normalized-action circles

One source ball supports the common free-centered action charts and
the vanishing unweighted quotient periods. The exact critical
midpoint identity factors each action through the squared periodic
gap and its normalized circle candidate. For a nonzero gap this
identifies the candidate with the raw quotient; at a collapsed gap
the Cauchy formula identifies it with the prescribed midpoint value.
Thus the circle candidate and the chart-independent normalized action
agree on one complex neighborhood for all distant indices.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On one complex source ball, every sufficiently distant free-circle
candidate equals the chart-independent normalized action, including
at complex collapsed gaps. The same circle exactly factors the glued
indexed action through the squared periodic gap. -/
theorem exists_local_sourceNormalizedAction_uniform_circle_complex_agreement
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ r : ℝ, 0 < r ∧
      ∀ ψ ∈ ball φ r, ∀ n : ℤ, K ≤ n.natAbs →
        sourceNormalizedActionCircleCandidate hp hp1 n
            ((Real.pi:ℂ)*n) (Real.pi/8) ψ =
          sourceNormalizedActionComplexExtension hp hp1 n ψ ∧
        sourceComplexAction hp hp1 n ψ =
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
            sourceNormalizedActionCircleCandidate hp hp1 n
              ((Real.pi:ℂ)*n) (Real.pi/8) ψ := by
  obtain ⟨K₀,r₀,hr₀,hzero⟩ :=
    exists_local_source_distantCriticalRootRatio_freeCircle_zero hp hp1 φ hreal
  obtain ⟨K₁,r₁,hr₁,haction⟩ :=
    exists_local_sourceComplexAction_eq_free_eighth_circle_tail hp hp1 φ hreal
  obtain ⟨Kg,Vg,hVgopen,hφVg,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data hp hp1 φ hreal
  obtain ⟨WE,hWEopen,hrealE,hEdata⟩ :=
    exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  obtain ⟨Wx,hWxopen,_,hrealx,hexact⟩ :=
    exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
  obtain ⟨rw,hrw,hrwsub⟩ := Metric.mem_nhds_iff.mp
    (((hVgopen.inter hWEopen).inter hWxopen).mem_nhds
      ⟨⟨hφVg,hrealE hreal⟩,hrealx hreal⟩)
  let K := max K₀ (max K₁ Kg)
  let r := min r₀ (min r₁ rw)
  have hr : 0 < r := lt_min hr₀ (lt_min hr₁ hrw)
  refine ⟨K,r,hr,?_⟩
  intro ψ hψ n hn
  have hψ₀ : ψ ∈ ball φ r₀ :=
    mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hψ) (min_le_left _ _))
  have hψ₁ : ψ ∈ ball φ r₁ :=
    mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hψ)
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hψw : ψ ∈ ball φ rw :=
    mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hψ)
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hψdata := hrwsub hψw
  have hK₀ : K₀ ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hK₁ : K₁ ≤ n.natAbs :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hKg : Kg ≤ n.natAbs :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  let c : ℂ := (Real.pi:ℂ)*n
  let R : ℝ := Real.pi/8
  obtain ⟨hseg,hother,_,_,_⟩ := hgeom ψ hψdata.1.1 n hKg
  have hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hseg hother
  have hzseg : ∀ z ∈ sphere c R,
      z ∉ sourcePeriodicSegment hp hp1 ψ n := by
    intro z hz
    exact hcircle hz n
  have hE : AnalyticOnNhd ℂ
      (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall c R) := by
    intro z hz
    exact hEdata ψ hψdata.1.2 n z (hother hz)
  have hcircleFactor := sourceActionCircle_eq_squaredGap_mul_kernel
    hp hp1 ψ n c R
    (canonicalCriticalGapQuotient hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (by positivity : 0 ≤ R) hcircle hzseg
    (hzero ψ hψ₀ n hK₀) hE (hexact ψ hψdata.2 n).2
  have hfactor : sourceComplexAction hp hp1 n ψ =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
        sourceNormalizedActionCircleCandidate hp hp1 n c R ψ :=
    (haction ψ hψ₁ n hK₁).trans hcircleFactor
  refine ⟨?_,hfactor⟩
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · have hcollapsed :=
      sourceNormalizedActionCircleCandidate_eq_collapsedCandidate_of_gap_zero
        hp hp1 ψ n c R (by positivity) hgap hseg hE
    simpa only [sourceNormalizedActionComplexExtension,
      sourceNormalizedActionRealExtension,if_pos hgap] using hcollapsed
  · have hraw : sourceRawNormalizedAction hp hp1 n ψ =
        sourceNormalizedActionCircleCandidate hp hp1 n c R ψ := by
      unfold sourceRawNormalizedAction
      rw [hfactor]
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hgap)
    simpa only [sourceNormalizedActionComplexExtension,
      sourceNormalizedActionRealExtension,if_neg hgap] using hraw.symm

end NLS.ZakharovShabat
