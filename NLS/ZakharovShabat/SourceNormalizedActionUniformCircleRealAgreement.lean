import NLS.ZakharovShabat.SourceRealActionUniformTailCircle
import NLS.ZakharovShabat.SourceCriticalRootRatioAnyCircleZero

/-!
# Real-type agreement of the common normalized contour candidate

On a real-type source, the unweighted critical-root quotient integral
vanishes on every valid circle, for open and collapsed gaps. The
recentered action therefore factors through the normalized contour
candidate. Combining this with the free-circle real-action formula
identifies the candidate with the prescribed normalized action.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The unweighted critical-root quotient integral vanishes on any
valid enclosing circle at a real-type source, whether its selected
gap is open or collapsed. -/
theorem sourceCriticalRootRatio_enclosingCircleIntegral_zero_of_realType_allGaps
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0 := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  by_cases hopen : l.re < r.re
  · change (∮ z in C(c,R),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z) = 0
    exact sourceCriticalRootRatio_enclosingCircleIntegral_eq_zero_of_realType
      hp hp1 ψ hreal n hopen c R hR hseg hother
  · have hle : l.re ≤ r.re :=
      re_le_of_complexLexLE
        ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ)).2.1 n)
    have hre : l.re = r.re := le_antisymm hle (le_of_not_gt hopen)
    obtain ⟨hlim,hrim⟩ :=
      canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ)
        (isRealType_periodOnePotential ψ hreal) n
    have he : l = r := Complex.ext hre (hlim.trans hrim.symm)
    have hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0 := by
      rw [sourcePeriodicGapDisplacement_apply]
      change r-l=0
      exact sub_eq_zero.mpr he.symm
    have hboundary : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
      sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hseg hother
    obtain ⟨W,_,hrealW,hcollapsed⟩ :=
      exists_global_sourceCriticalRootRatio_circleIntegral_zero_of_zeroGap hp hp1
    change (∮ z in C(c,R),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z) = 0
    exact hcollapsed ψ (hrealW hreal) n hgap c R hR.le hother hboundary

/-- On a real-type source, any valid circle already known to compute
the indexed real action gives the chart-independent normalized-action
value, including at a collapsed gap. -/
theorem sourceNormalizedActionCircleCandidate_eq_complexExtension_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hrealAction : sourceRealAction hp hp1 ψ hreal n =
      sourceActionCircle hp hp1 ψ c R) :
    sourceNormalizedActionCircleCandidate hp hp1 n c R ψ =
      sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  obtain ⟨W₁,_,hreal₁,hEdata⟩ :=
    exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  have hE : AnalyticOnNhd ℂ
      (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall c R) := by
    intro z hz
    exact hEdata ψ (hreal₁ hreal) n z (hother hz)
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · have hcollapsed :=
      sourceNormalizedActionCircleCandidate_eq_collapsedCandidate_of_gap_zero
        hp hp1 ψ n c R hR hgap hseg hE
    simpa only [sourceNormalizedActionComplexExtension,
      sourceNormalizedActionRealExtension,if_pos hgap] using hcollapsed
  · obtain ⟨W₂,_,_,hreal₂,hexact⟩ :=
      exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
    have hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
      sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hseg hother
    have hzseg : ∀ z ∈ sphere c R,
        z ∉ sourcePeriodicSegment hp hp1 ψ n := by
      intro z hz
      exact hcircle hz n
    have hzero :=
      sourceCriticalRootRatio_enclosingCircleIntegral_zero_of_realType_allGaps
        hp hp1 ψ hreal n c R hR hseg hother
    have hfactor := sourceActionCircle_eq_squaredGap_mul_kernel
      hp hp1 ψ n c R
      (canonicalCriticalGapQuotient hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      hR.le hcircle hzseg hzero hE (hexact ψ (hreal₂ hreal) n).2
    have hsource : sourceComplexAction hp hp1 n ψ =
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
          sourceNormalizedActionCircleCandidate hp hp1 n c R ψ := by
      calc
        sourceComplexAction hp hp1 n ψ =
            sourceRealAction hp hp1 ψ hreal n :=
          sourceComplexAction_eq_sourceRealAction hp hp1 n ψ hreal
        _ = sourceActionCircle hp hp1 ψ c R := hrealAction
        _ = _ := hfactor
    have hraw : sourceRawNormalizedAction hp hp1 n ψ =
        sourceNormalizedActionCircleCandidate hp hp1 n c R ψ := by
      unfold sourceRawNormalizedAction
      rw [hsource]
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hgap)
    simpa only [sourceNormalizedActionComplexExtension,
      sourceNormalizedActionRealExtension,if_neg hgap] using hraw.symm

/-- On one neighborhood, every distant common-circle candidate
agrees with the existing normalized-action extension at real-type
sources. The common cutoff is independent of the signed index. -/
theorem exists_local_sourceNormalizedAction_uniform_circle_real_agreement
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
        ∀ n : ℤ, K ≤ n.natAbs →
          sourceNormalizedActionCircleCandidate hp hp1 n
              ((Real.pi:ℂ)*n) (Real.pi/8) ψ =
            sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  obtain ⟨Kr,Vr,hVropen,hφVr,hrealAction⟩ :=
    exists_local_sourceRealAction_eq_free_eighth_circle_tail hp hp1 φ hφ
  obtain ⟨Kc,Vc,hVcopen,hφVc,hcircle⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data hp hp1 φ hφ
  let K := max Kr Kc
  refine ⟨K,Vr ∩ Vc,hVropen.inter hVcopen,⟨hφVr,hφVc⟩,?_⟩
  intro ψ hψ hreal n hn
  have hKr : Kr ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hKc : Kc ≤ n.natAbs := le_trans (le_max_right _ _) hn
  obtain ⟨hseg,hother,_,_,_⟩ := hcircle ψ hψ.2 n hKc
  exact sourceNormalizedActionCircleCandidate_eq_complexExtension_of_realType
    hp hp1 ψ hreal n ((Real.pi:ℂ)*n) (Real.pi/8)
      (by positivity) hseg hother (hrealAction ψ hψ.1 hreal n hKr)

end NLS.ZakharovShabat
