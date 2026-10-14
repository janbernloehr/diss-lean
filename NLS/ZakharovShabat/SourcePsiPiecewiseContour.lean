import NLS.ZakharovShabat.SourcePsiEquationContourHomotopy
import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle
import NLS.ZakharovShabat.SourceFiniteGapExterior
import NLS.ComplexAnalysis.PiecewiseContourOuterPeriod
import NLS.ComplexAnalysis.SegmentIsolatingCircles

/-!
# Psi periods on arbitrary original circuits

The literal psi/root integral has the dissertation's factor 1/(2π).
Original isolating circles give the same period, and every piecewise C¹
loop in an original cut disk computes that period times its winding.
No specified homotopy or noncollapsed-gap assumption is required.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal normalized psi integral on a finite piecewise C¹ loop. -/
def sourcePsiCircuit (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p)
    (ψ : CoeffPair p) (Γ : PiecewiseC1Loop) : ℂ :=
  (2*Real.pi:ℂ)⁻¹*Γ.integral (fun z => sourcePsiCandidate n (z,a)/sourceCanonicalRoot hp hp1 ψ z)

/-- Circle and piecewise-loop normalizations agree exactly. -/
theorem sourcePsiCircuit_circle (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p)
    (ψ : CoeffPair p) (c : ℂ) (r : ℝ) :
    sourcePsiCircuit hp hp1 n a ψ (PiecewiseC1Loop.circle c r) = sourcePsiContour hp hp1 n a ψ c r := by
  simp only [sourcePsiCircuit,sourcePsiContour,sourcePsiContourIntegrandJoint,PiecewiseC1Loop.integral_circle]

/-- Original circles from different isolating families have the same psi period. -/
theorem SourceCriticalRootPeriodCircle.psiContour_eq
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D E : SourceCriticalRootPeriodCircle hp hp1 ψ m) (n : ℤ) (a : Coeff p) :
    sourcePsiContour hp hp1 n a ψ (D.center:ℂ) D.radius =
      sourcePsiContour hp hp1 n a ψ (E.center:ℂ) E.radius :=
  sourcePsiContour_eq_of_homotopy_range hp hp1 n a ψ _ _ _ _
    (ContinuousMap.Homotopy.affine
      (circlePath (D.center:ℂ) D.radius : C(I,ℂ)) (circlePath (E.center:ℂ) E.radius))
    (affineHomotopy_loop (γ₁ := circlePath (D.center:ℂ) D.radius)
      (γ₂ := circlePath (E.center:ℂ) E.radius))
    (D.homotopy_range E)
    (affineHomotopy_contDiffOn (circlePath_contDiffOn _ _) (circlePath_contDiffOn _ _))

/-- The original outer circle computes every loop period in the entire cut disk. -/
theorem SourceCriticalRootPeriodCircle.psiCircuit_eq_mul_winding
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) (n : ℤ) (a : Coeff p)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m)) :
    sourcePsiCircuit hp hp1 n a ψ Γ =
      sourcePsiContour hp hp1 n a ψ (D.center:ℂ) D.radius * Γ.windingIntegral
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) := by
  obtain ⟨r,s,hr,hrs,hsR,hgap⟩ := exists_nested_radii_of_segment_subset_ball _ _ (D.center:ℂ) D.radius D.gap
  let f : ℂ → ℂ := fun z => sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))
  have hf : AnalyticOnNhd ℂ f (closedBall (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m) :=
    (analyticOnNhd_sourcePsiContourIntegrand_fixed hp hp1 n a ψ).mono (by
      intro z hz k
      by_cases hk : k = m
      · subst k; exact hz.2
      · exact D.closedBall_subset_omittedDomain hz.1 k hk)
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ m
  have he := Γ.integral_eq_outerCircleIntegral_mul_winding_of_starConvex_cut f (D.center:ℂ)
    _ r D.radius hr (hrs.trans hsR) _ (isCompact_sourcePeriodicSegment hp hp1 ψ m).isClosed
    hmid ((convex_segment _ _).starConvex hmid) hgap hf hΓ
  change (2*Real.pi:ℂ)⁻¹*Γ.integral f = _
  rw [he,← mul_assoc]
  rfl

end NLS.ZakharovShabat
