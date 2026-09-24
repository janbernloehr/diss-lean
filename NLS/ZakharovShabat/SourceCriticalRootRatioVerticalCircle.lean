import NLS.ZakharovShabat.SourceCriticalRootRatioNearMidpointCircle
import NLS.ComplexAnalysis.VerticalCircleHomotopy

/-!
# Vertical recentering of real-type quotient contours

For real-type sources, every periodic gap lies on the real axis. A
circle can move its center vertically while preserving its real-axis
intersections, so a circle initially avoiding every gap continues to
avoid them throughout the deformation.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The critical-root quotient has the same integral on a circle and
on its real-centered vertical projection, provided the original
circle avoids all periodic gaps. -/
theorem sourceCriticalRootRatio_circleIntegral_eq_verticalProjection
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (q R : ℝ) (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hsq : q^2+c.im^2=R^2)
    (hboundary : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    (∮ z in C((c.re:ℂ),q),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z) =
    ∮ z in C(c,R),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z := by
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  let H := NLS.ComplexAnalysis.verticalCircleHomotopy c q R hq hR hsq
  have hloop := NLS.ComplexAnalysis.verticalCircleHomotopy_loop
    c q R hq hR hsq
  have hsmooth := NLS.ComplexAnalysis.verticalCircleHomotopy_slice_contDiffOn
    c q R hq hR hsq
  have havoid (s u : I) : H (s,u) ∈
      sourceCanonicalRootDomain hp hp1 ψ := by
    let z := H (s,u)
    by_cases hz : z.im = 0
    · have hsphere : z ∈ sphere
          (NLS.ComplexAnalysis.verticalCircleCenter c (s:ℝ))
          (NLS.ComplexAnalysis.verticalCircleRadius c q (s:ℝ)) := by
        change circleMap (NLS.ComplexAnalysis.verticalCircleCenter c (s:ℝ))
          (NLS.ComplexAnalysis.verticalCircleRadius c q (s:ℝ))
          ((2*Real.pi)*(u:ℝ)) ∈ sphere _ _
        exact circleMap_mem_sphere _ (Real.sqrt_nonneg _) _
      have horig : z ∈ sphere c R :=
        (NLS.ComplexAnalysis.verticalCircle_real_sphere_iff
          c z q R (s:ℝ) hz hR hsq).mp hsphere
      exact hboundary horig
    · exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal z hz
  have heq := sourceCriticalRootRatio_curveIntegral_eq_of_continuous_smooth_homotopy
    hp hp1 ψ hreal H hloop hsmooth havoid
  calc
    (∮ z in C((c.re:ℂ),q), f z) =
        ∫ᶜ z in NLS.ComplexAnalysis.circlePath (c.re:ℂ) q,
          NLS.ComplexAnalysis.holomorphicOneForm f z :=
      (NLS.ComplexAnalysis.curveIntegral_circlePath f _ _).symm
    _ = ∫ᶜ z in NLS.ComplexAnalysis.circlePath c R,
          NLS.ComplexAnalysis.holomorphicOneForm f z := heq
    _ = (∮ z in C(c,R), f z) :=
      NLS.ComplexAnalysis.curveIntegral_circlePath f c R

/-- Any gap-enclosing circle at a real-type source projects to a
real-centered gap-enclosing circle with the same quotient integral.
The projected filled disc also avoids every other periodic gap. -/
theorem exists_sourceCriticalRootRatio_verticalProjection_enclosingCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    ∃ q : ℝ, 0 < q ∧
      sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c.re:ℂ) q ∧
      closedBall (c.re:ℂ) q ⊆
        sourceStandardRootOmittedDomain hp hp1 ψ n ∧
      (∮ z in C((c.re:ℂ),q),
        deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z) =
      ∮ z in C(c,R),
        deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  have hlseg : l ∈ sourcePeriodicSegment hp hp1 ψ n :=
    left_mem_segment ℝ _ _
  have hlim : l.im = 0 :=
    (canonicalPeriodicEndpoints_im_eq_zero_of_realType
      hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) n).1
  obtain ⟨q,hq,hsq⟩ :=
    NLS.ComplexAnalysis.exists_verticalCircleRadius_of_real_point_mem_ball
      c l R hlim (hseg hlseg)
  have hboundary : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hseg hother
  refine ⟨q,hq,?_,?_,?_⟩
  · intro z hz
    have hzim := sourcePeriodicSegment_im_eq_zero_of_realType
      hp hp1 ψ hreal n z hz
    exact (NLS.ComplexAnalysis.real_mem_ball_verticalCircle_iff
      c z q R hzim hq.le hR.le hsq).mp (hseg hz)
  · intro z hz m hm
    by_cases hzim : z.im = 0
    · have horig : z ∈ closedBall c R :=
        (NLS.ComplexAnalysis.real_mem_closedBall_verticalCircle_iff
          c z q R hzim hq.le hR.le hsq).mpr hz
      exact hother horig m hm
    · intro hmem
      exact hzim (sourcePeriodicSegment_im_eq_zero_of_realType
        hp hp1 ψ hreal m z hmem)
  · exact sourceCriticalRootRatio_circleIntegral_eq_verticalProjection
      hp hp1 ψ hreal c q R hq.le hR.le hsq hboundary

end NLS.ZakharovShabat
