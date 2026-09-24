import NLS.ComplexAnalysis.IntegrableDerivativeBoundary
import NLS.ZakharovShabat.SourceCriticalRootRatioHalfPlanePrimitive
import NLS.ZakharovShabat.SourceCriticalRootRatioEndpointConnectorIntegrable

/-!
# Radial boundary limits of critical-root quotient primitives

The quotient is integrable on short vertical rays from either endpoint
of an open real-type gap. Therefore any half-plane primitive has a
finite limit along each of those rays, from above and from below.
These ray limits are a step toward a path-independent boundary value.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every upper-half-plane primitive of the critical-root quotient has
a finite limit along the upward vertical ray at either gap endpoint. -/
theorem exists_sourceCriticalRootRatio_upperPrimitive_vertical_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ ({(-1:ℝ),1} : Set ℝ),
      ∀ F : ℂ → ℂ,
        (∀ z : ℂ, 0 < z.im →
          HasDerivAt F
            (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
              sourceCanonicalRoot hp hp1 ψ z) z) →
        ∃ A : ℂ, Tendsto
          (fun y : ℝ => F (sourceCanonicalRootGapPoint hp hp1 ψ n t +
            (y:ℂ)*Complex.I)) (𝓝[>] (0:ℝ)) (𝓝 A) ∧
          ∀ y ∈ Ioo (0:ℝ) (ε/2),
            F (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*Complex.I) =
              A + ∫ v in Ioc (0:ℝ) y,
                (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
                  (sourceCanonicalRootGapPoint hp hp1 ψ n t + (v:ℂ)*Complex.I) /
                  sourceCanonicalRoot hp hp1 ψ
                    (sourceCanonicalRootGapPoint hp hp1 ψ n t + (v:ℂ)*Complex.I)) *
                  Complex.I := by
  obtain ⟨ε,hε,hint⟩ :=
    exists_sourceCriticalRootRatio_upperEndpointConnector_integrable
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro t ht F hF
  let c := sourceCanonicalRootGapPoint hp hp1 ψ n t
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hcim : c.im = 0 := by
    rcases (by simpa using ht : t = -1 ∨ t = 1) with h | h
    · dsimp [c]
      rw [h, sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n]
      exact hl
    · dsimp [c]
      rw [h, sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n]
      exact hr
  have hpoint (y : ℝ) (hy : y ∈ Ioo (0:ℝ) ε) :
      0 < (c+(y:ℂ)*Complex.I).im := by
    simpa [hcim] using hy.1
  exact NLS.ComplexAnalysis.exists_primitive_vertical_ray_limit
    (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z) F c ε hε
    (fun y hy => hF _ (hpoint y hy)) (hint t ht)

/-- The corresponding finite primitive limits along downward rays. -/
theorem exists_sourceCriticalRootRatio_lowerPrimitive_vertical_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ ({(-1:ℝ),1} : Set ℝ),
      ∀ F : ℂ → ℂ,
        (∀ z : ℂ, z.im < 0 →
          HasDerivAt F
            (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
              sourceCanonicalRoot hp hp1 ψ z) z) →
        ∃ A : ℂ, Tendsto
          (fun y : ℝ => F (sourceCanonicalRootGapPoint hp hp1 ψ n t +
            ((-y:ℝ):ℂ)*Complex.I)) (𝓝[>] (0:ℝ)) (𝓝 A) ∧
          ∀ y ∈ Ioo (0:ℝ) (ε/2),
            F (sourceCanonicalRootGapPoint hp hp1 ψ n t +
              ((-y:ℝ):ℂ)*Complex.I) = A +
                ∫ v in Ioc (0:ℝ) y,
                  (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
                    (sourceCanonicalRootGapPoint hp hp1 ψ n t +
                      ((-v:ℝ):ℂ)*Complex.I) /
                    sourceCanonicalRoot hp hp1 ψ
                      (sourceCanonicalRootGapPoint hp hp1 ψ n t +
                        ((-v:ℝ):ℂ)*Complex.I)) * (-Complex.I) := by
  obtain ⟨ε,hε,hint⟩ :=
    exists_sourceCriticalRootRatio_lowerEndpointConnector_integrable
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro t ht F hF
  let c := sourceCanonicalRootGapPoint hp hp1 ψ n t
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hcim : c.im = 0 := by
    rcases (by simpa using ht : t = -1 ∨ t = 1) with h | h
    · dsimp [c]
      rw [h, sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n]
      exact hl
    · dsimp [c]
      rw [h, sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n]
      exact hr
  have hpoint (y : ℝ) (hy : y ∈ Ioo (0:ℝ) ε) :
      (c+((-y:ℝ):ℂ)*Complex.I).im < 0 := by
    simpa [hcim] using (neg_lt_zero.mpr hy.1)
  exact NLS.ComplexAnalysis.exists_primitive_downward_ray_limit
    (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z) F c ε hε
    (fun y hy => hF _ (hpoint y hy)) (hint t ht)

end NLS.ZakharovShabat
