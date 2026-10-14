import NLS.ZakharovShabat.SourcePsiPiecewiseContour

/-!
# The functional in equations (2.22) and (2.23)

The functional Aₘⁿ is the actual, unnormalized contour integral multiplied
by n-m. Arbitrary original circuits compute the circle functional times
their winding, for every local analytic numerator on the filled disk.
The entire product in (2.23) is a specialization, with no gap-location
assumption on its arbitrary displacement vector.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source functional Aₘⁿ, with no normalized-period prefactor. -/
def sourceGapFunctional (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (ψ : CoeffPair p) (Γ : PiecewiseC1Loop) (f : ℂ → ℂ) : ℂ :=
  ((n-m:ℤ):ℂ)*Γ.integral (fun z => f z/sourceCanonicalRoot hp hp1 ψ z)

/-- Substituting the arbitrary product (2.23) gives exactly (2.22) on a circle. -/
theorem sourceGapFunctional_candidate_circle (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (c : ℂ) (r : ℝ) :
    sourceGapFunctional hp hp1 n m ψ (PiecewiseC1Loop.circle c r)
      (fun z => sourcePsiCandidate n (z,a)) = sourcePsiEquationCoordinate hp hp1 n m a ψ c r := by
  rw [sourcePsiEquationCoordinate_eq_raw_circleIntegral]
  simp only [sourceGapFunctional,PiecewiseC1Loop.integral_circle,sourcePsiContourIntegrandJoint]

/-- A local numerator on the filled original disk has the usual winding period. -/
theorem SourceCriticalRootPeriodCircle.localNumerator_circuit_eq
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (D.center:ℂ) D.radius))
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m)) :
    Γ.integral (fun z => f z/sourceCanonicalRoot hp hp1 ψ z) =
      (∮ z in C((D.center:ℂ),D.radius), f z/sourceCanonicalRoot hp hp1 ψ z)*
        Γ.windingIntegral
          (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) := by
  obtain ⟨r,s,hr,hrs,hsR,hgap⟩ := exists_nested_radii_of_segment_subset_ball _ _ (D.center:ℂ) D.radius D.gap
  have hquot : AnalyticOnNhd ℂ (fun z => f z/sourceCanonicalRoot hp hp1 ψ z)
      (closedBall (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m) := by
    intro z hz
    have hzroot : z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
      intro k
      by_cases hkm : k = m
      · subst k; exact hz.2
      · exact D.closedBall_subset_omittedDomain hz.1 k hkm
    exact (hf z hz.1).div (sourceCanonicalRoot_analyticOnNhd hp hp1 ψ z hzroot)
      (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z hzroot)
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ m
  exact Γ.integral_eq_outerCircleIntegral_mul_winding_of_starConvex_cut _ (D.center:ℂ)
    _ r D.radius hr (hrs.trans hsR) _ (isCompact_sourcePeriodicSegment hp hp1 ψ m).isClosed
    hmid ((convex_segment _ _).starConvex hmid) hgap hquot hΓ

/-- Every original circuit gives the circle functional multiplied by its winding. -/
theorem SourceCriticalRootPeriodCircle.gapFunctional_eq_mul_winding
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) (n : ℤ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (D.center:ℂ) D.radius))
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m)) :
    sourceGapFunctional hp hp1 n m ψ Γ f =
      sourceGapFunctional hp hp1 n m ψ (PiecewiseC1Loop.circle (D.center:ℂ) D.radius) f *
        Γ.windingIntegral
          (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) := by
  simp only [sourceGapFunctional,PiecewiseC1Loop.integral_circle]
  rw [D.localNumerator_circuit_eq f hf Γ hΓ,mul_assoc]

/-- Equation (2.22) on every original circuit, for an arbitrary ℓᵖ displacement input. -/
theorem SourceCriticalRootPeriodCircle.psiEquation_circuit
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) (n : ℤ) (a : Coeff p)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m)) :
    sourceGapFunctional hp hp1 n m ψ Γ (fun z => sourcePsiCandidate n (z,a)) =
      sourcePsiEquationCoordinate hp hp1 n m a ψ (D.center:ℂ) D.radius *
        Γ.windingIntegral
          (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) := by
  have hf : AnalyticOnNhd ℂ (fun z => sourcePsiCandidate n (z,a)) (closedBall (D.center:ℂ) D.radius) := by
    intro z _
    exact (analyticOnNhd_sourcePsiCandidate hp hp1 n (z,a) (mem_univ _)).comp
      (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  rw [D.gapFunctional_eq_mul_winding n (fun z => sourcePsiCandidate n (z,a)) hf Γ hΓ,
    sourceGapFunctional_candidate_circle]

/-- Original circle families define the same scalar equation coordinate. -/
theorem SourceCriticalRootPeriodCircle.psiEquation_eq
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D E : SourceCriticalRootPeriodCircle hp hp1 ψ m) (n : ℤ) (a : Coeff p) :
    sourcePsiEquationCoordinate hp hp1 n m a ψ (D.center:ℂ) D.radius =
      sourcePsiEquationCoordinate hp hp1 n m a ψ (E.center:ℂ) E.radius := by
  simp only [sourcePsiEquationCoordinate,D.psiContour_eq E n a]


end NLS.ZakharovShabat
