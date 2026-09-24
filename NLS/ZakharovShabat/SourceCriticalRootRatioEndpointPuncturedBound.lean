import NLS.ZakharovShabat.SourceCriticalRootRatioEndpointCircleBound

/-!
# Quotient bound throughout punctured endpoint neighborhoods

The endpoint-circle estimate is radial, so it applies pointwise to
every gap-avoiding point in a small punctured disc around either open
real-type gap endpoint. This is the geometric input for curved
connectors starting at the branch points.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The critical-root quotient has inverse-square-root growth at
every gap-avoiding point near either endpoint of an open real gap. -/
theorem exists_sourceCriticalRootRatio_endpointPunctured_weighted_bound
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
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ c ∈ ({l,r} : Set ℂ), ∀ z : ℂ,
        z ∈ sourceCanonicalRootDomain hp hp1 ψ →
        0 < ‖c-z‖ → ‖c-z‖ ≤ ε →
        ‖(deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
            sourceCanonicalRoot hp hp1 ψ z) *
          ((Real.sqrt (((r.re-l.re)/2)*‖c-z‖) : ℝ) : ℂ)‖ ≤ M := by
  dsimp only
  obtain ⟨ε,M,hε,hM,hcircle⟩ :=
    exists_sourceCriticalRootRatio_endpointCircle_weighted_bound
      hp hp1 ψ hreal n hopen
  refine ⟨ε,M,hε,hM,?_⟩
  intro c hc z hz hpos hεz
  exact hcircle ‖c-z‖ ⟨hpos,hεz⟩ c hc z hz rfl

end NLS.ZakharovShabat
