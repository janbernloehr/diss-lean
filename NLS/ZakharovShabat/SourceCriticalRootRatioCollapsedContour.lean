import NLS.ZakharovShabat.SourceCriticalRootRatioCollapsed
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The closed-contour identity at a collapsed periodic gap

The critical derivative divided by the canonical root extends
analytically across a collapsed gap. Hence its integral around any
circle whose filled disc avoids the other gaps vanishes. This is the
collapsed-gap case of the contour conclusion in Lemma 10.11(ii).
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The deleted critical-root quotient integrates to zero around any
filled circle inside its omitted-gap domain. -/
theorem exists_global_sourceCriticalRootRatioExtension_circleIntegral_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ,
        sourcePeriodicGapDisplacement hp hp1 ψ n = 0 →
          ∀ c : ℂ, ∀ r : ℝ, 0 ≤ r →
            closedBall c r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
              (∮ z in C(c,r), sourceCriticalRootRatioExtension hp hp1 n ψ z) = 0 := by
  obtain ⟨W,hWopen,hreal,hdata⟩ :=
    exists_global_sourceCriticalRootRatio_analytic_of_zeroGap hp hp1
  refine ⟨W,hWopen,hreal,?_⟩
  intro ψ hψ n hgap c r hr hfilled
  have hanalytic := (hdata ψ hψ n hgap).1
  have hd : DifferentiableOn ℂ (sourceCriticalRootRatioExtension hp hp1 n ψ)
      (closedBall c r) := by
    intro z hz
    exact (hanalytic z (hfilled hz)).differentiableAt.differentiableWithinAt
  exact (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall)
    hd.continuousOn).circleIntegral_eq_zero hr

/-- On a circle where the original quotient is defined, its integral
agrees with the analytic extension and therefore vanishes. -/
theorem exists_global_sourceCriticalRootRatio_circleIntegral_zero_of_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ,
        sourcePeriodicGapDisplacement hp hp1 ψ n = 0 →
          ∀ c : ℂ, ∀ r : ℝ, 0 ≤ r →
            closedBall c r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
            sphere c r ⊆ sourceCanonicalRootDomain hp hp1 ψ →
              (∮ z in C(c,r),
                deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
                  sourceCanonicalRoot hp hp1 ψ z) = 0 := by
  obtain ⟨W,hWopen,hreal,hdata⟩ :=
    exists_global_sourceCriticalRootRatio_analytic_of_zeroGap hp hp1
  refine ⟨W,hWopen,hreal,?_⟩
  intro ψ hψ n hgap c r hr hfilled hboundary
  have hanalytic := (hdata ψ hψ n hgap).1
  have heq := (hdata ψ hψ n hgap).2
  have hd : DifferentiableOn ℂ (sourceCriticalRootRatioExtension hp hp1 n ψ)
      (closedBall c r) := by
    intro z hz
    exact (hanalytic z (hfilled hz)).differentiableAt.differentiableWithinAt
  have hzero : (∮ z in C(c,r), sourceCriticalRootRatioExtension hp hp1 n ψ z) = 0 :=
    (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall)
      hd.continuousOn).circleIntegral_eq_zero hr
  calc
    (∮ z in C(c,r),
        deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z) =
      (∮ z in C(c,r), sourceCriticalRootRatioExtension hp hp1 n ψ z) := by
        apply circleIntegral.integral_congr hr
        intro z hz
        exact (heq z (hboundary hz)).symm
    _ = 0 := hzero

end NLS.ZakharovShabat
