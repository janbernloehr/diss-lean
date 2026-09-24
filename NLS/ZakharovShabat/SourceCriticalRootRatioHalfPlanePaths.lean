import NLS.ComplexAnalysis.ConvexHolomorphicPathIntegral
import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumPath
import NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy

/-!
# Path independence above and below real-type spectral gaps

All periodic gap segments of a real-type source lie on the real axis.
The upper and lower half-planes are convex and avoid every gap, so the
critical-root quotient has equal integrals along any two smooth paths
in either half-plane with the same endpoints.
-/

noncomputable section
open Set Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem convex_upperHalfPlane :
    Convex ℝ {z : ℂ | 0 < z.im} := by
  have hlin : IsLinearMap ℝ (fun z : ℂ => z.im) := by
    constructor
    · intro x y
      simp
    · intro c x
      simp
  exact convex_halfSpace_gt hlin 0

private theorem convex_lowerHalfPlane :
    Convex ℝ {z : ℂ | z.im < 0} := by
  have hlin : IsLinearMap ℝ (fun z : ℂ => z.im) := by
    constructor
    · intro x y
      simp
    · intro c x
      simp
  exact convex_halfSpace_lt hlin 0

/-- At a real-type source, the quotient integral is independent of a
smooth path within the upper half-plane, for fixed endpoints there. -/
theorem sourceCriticalRootRatio_upperHalfPlane_pathIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {a b : ℂ} (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 2 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 2 γ₂.extend (Icc 0 1))
    (hγ₁upper : ∀ u : I, 0 < (γ₁ u).im)
    (hγ₂upper : ∀ u : I, 0 < (γ₂ u).im) :
    (∫ᶜ z in γ₁, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) =
    ∫ᶜ z in γ₂, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z := by
  apply NLS.ComplexAnalysis.curveIntegral_eq_of_convex_paths
    _ _ convex_upperHalfPlane _ γ₁ γ₂ hγ₁ hγ₂ hγ₁upper hγ₂upper
  intro z hz
  exact (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z
    (sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal z
      (ne_of_gt hz))).differentiableAt

/-- The corresponding path-independence theorem below the real axis. -/
theorem sourceCriticalRootRatio_lowerHalfPlane_pathIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {a b : ℂ} (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 2 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 2 γ₂.extend (Icc 0 1))
    (hγ₁lower : ∀ u : I, (γ₁ u).im < 0)
    (hγ₂lower : ∀ u : I, (γ₂ u).im < 0) :
    (∫ᶜ z in γ₁, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) =
    ∫ᶜ z in γ₂, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z := by
  apply NLS.ComplexAnalysis.curveIntegral_eq_of_convex_paths
    _ _ convex_lowerHalfPlane _ γ₁ γ₂ hγ₁ hγ₂ hγ₁lower hγ₂lower
  intro z hz
  exact (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z
    (sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal z
      (ne_of_lt hz))).differentiableAt

end NLS.ZakharovShabat
