import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import NLS.ZakharovShabat.SourceCriticalRootRatioPrimitiveBoundary

/-!
# Exact zero for arbitrary smooth integrable endpoint paths

The primitive has the same full boundary value at both ends of an
open real-type gap. Thus no detour decomposition is needed: every
smooth, curve-integrable path whose interior stays in a single open
half-plane has zero critical-root quotient integral.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any `C¹` curve-integrable upper-half-plane path from the left to
right endpoint of an open real-type gap has zero quotient integral. -/
theorem sourceCriticalRootRatio_upperSmoothEndpointPath_integral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let f : ℂ → ℂ := fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z
    ∀ γ : Path l r,
      ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
      (∀ t ∈ Ioo (0:ℝ) 1, 0 < (γ.extend t).im) →
      CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) γ →
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm f z) = 0 := by
  dsimp only
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  obtain ⟨F,hF⟩ := exists_sourceCriticalRootRatio_upperHalfPlane_primitive
    hp hp1 ψ hreal
  obtain ⟨A,hl,hr⟩ := sourceCriticalRootRatio_upperPrimitive_common_boundary_limit
    hp hp1 ψ hreal n hopen F hF
  intro γ hγ hupper hint
  exact NLS.ComplexAnalysis.curveIntegral_eq_zero_of_primitive_boundary_ends
    f F {z : ℂ | 0 < z.im} (fun z hz => hF z hz)
    γ hγ hupper hint hl hr

/-- Any `C¹` curve-integrable lower-half-plane path from the left to
right endpoint of an open real-type gap has zero quotient integral. -/
theorem sourceCriticalRootRatio_lowerSmoothEndpointPath_integral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let f : ℂ → ℂ := fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z
    ∀ γ : Path l r,
      ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
      (∀ t ∈ Ioo (0:ℝ) 1, (γ.extend t).im < 0) →
      CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) γ →
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm f z) = 0 := by
  dsimp only
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  obtain ⟨F,hF⟩ := exists_sourceCriticalRootRatio_lowerHalfPlane_primitive
    hp hp1 ψ hreal
  obtain ⟨A,hl,hr⟩ := sourceCriticalRootRatio_lowerPrimitive_common_boundary_limit
    hp hp1 ψ hreal n hopen F hF
  intro γ hγ hupper hint
  exact NLS.ComplexAnalysis.curveIntegral_eq_zero_of_primitive_boundary_ends
    f F {z : ℂ | z.im < 0} (fun z hz => hF z hz)
    γ hγ hupper hint hl hr

end NLS.ZakharovShabat
