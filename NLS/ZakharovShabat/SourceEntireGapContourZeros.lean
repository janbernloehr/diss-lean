import NLS.ZakharovShabat.SourceLocalGapContourZeros

/-!
# Entire-numerator specializations of local gap-contour zeros

The public entire-numerator results follow from the local statements.
Their original signatures remain available to the psi and limit-operator
constructions.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A zero contour of an entire numerator that is real on the real
axis forces a zero in the enclosed open real periodic gap. -/
theorem exists_sourceEntireNumerator_zero_on_openGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ)
    (hFreal : ∀ x : ℝ, (F (x:ℂ)).im = 0)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C((x:ℂ),R),
      F z /
        sourceCanonicalRoot hp hp1 ψ z) = 0) :
    ∃ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      F μ = 0 := by
  apply exists_sourceLocalNumerator_zero_on_openGap hp hp1 ψ hψ m F ?_ hopen
    x R hR (hF.mono (subset_univ _)) hseg hdom hcircle hzero
  intro z hz
  have hi := sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hψ m z hz
  have he : (z.re:ℂ) = z := by
    apply Complex.ext
    · rfl
    · simpa using hi.symm
  simpa only [he] using hFreal z.re

/-- A zero contour at a collapsed periodic gap forces any entire
numerator to vanish at the gap midpoint; no reality assumption is needed. -/
theorem sourceEntireNumerator_zero_at_collapsedGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (c₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c₀ R)
    (hdom : closedBall c₀ R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere c₀ R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C(c₀,R),
      F z /
        sourceCanonicalRoot hp hp1 ψ z) = 0) :
    F
      (sourceStandardRootMidpoint hp hp1 ψ m) = 0 := by
  exact sourceLocalNumerator_zero_at_collapsedGap hp hp1 ψ hψ m F hgap
    c₀ R hR (hF.mono (subset_univ _)) hmid hdom hcircle hzero

end NLS.ZakharovShabat
