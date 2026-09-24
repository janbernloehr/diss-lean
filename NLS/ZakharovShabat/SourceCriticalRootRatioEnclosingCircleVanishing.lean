import NLS.ZakharovShabat.SourceCriticalRootRatioRealCenteredCircleVanishing

/-!
# Vanishing on arbitrary enclosing circles at real-type sources

Vertical projection reduces an arbitrary complex-centered enclosing
circle to a real-centered one without changing its integral. A nested
circle homotopy then moves the real center to the gap midpoint, where
the integral is already known to vanish.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The critical-root quotient integrates to zero around every
circular contour that encloses one open real-type gap and whose filled
disc excludes all other gaps. The center is arbitrary. -/
theorem sourceCriticalRootRatio_enclosingCircleIntegral_eq_zero_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (∮ z in C(c,R),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z) = 0 := by
  obtain ⟨q,hq,hsegq,hotherq,heq⟩ :=
    exists_sourceCriticalRootRatio_verticalProjection_enclosingCircle
      hp hp1 ψ hreal n c R hR hseg hother
  have hzero := sourceCriticalRootRatio_realCenteredCircleIntegral_eq_zero
    hp hp1 ψ hreal n hopen c.re q hq hsegq hotherq
  exact heq.symm.trans hzero

end NLS.ZakharovShabat
