import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import NLS.ZakharovShabat.SourceCriticalRootRatioCurvedEndpointConnector
import NLS.ZakharovShabat.SourceCriticalRootRatioHalfPlanePrimitive

/-!
# Primitive limits along curved singular connectors

An integrable derivative gives a finite primitive limit along any
smooth, linearly departing connector in either open half-plane. The
connector integral is exactly the regular endpoint value minus that
pathwise limit. Equality of limits for different connector shapes is
a separate boundary-continuity question.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every upper-half-plane primitive has a finite limit along a short
curved connector leaving either endpoint of an open real gap. -/
theorem exists_sourceCriticalRootRatio_upperCurvedConnector_primitive_limit
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
    ∃ ε : ℝ, 0 < ε ∧ ∀ c ∈ ({l,r} : Set ℂ),
      ∀ {b : ℂ} (γ : Path c b),
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
        (∀ t ∈ Ioo (0:ℝ) 1, 0 < (γ.extend t).im) →
        0 < b.im →
        (∀ t ∈ Ioo (0:ℝ) 1,
          0 < ‖c-γ.extend t‖ ∧ ‖c-γ.extend t‖ ≤ ε) →
        (∃ k : ℝ, 0 < k ∧ ∀ t ∈ Ioo (0:ℝ) 1,
          k*t ≤ ‖c-γ.extend t‖) →
        ∀ F : ℂ → ℂ,
          (∀ z : ℂ, 0 < z.im → HasDerivAt F (f z) z) →
          ∃ A : ℂ,
            Tendsto (F ∘ γ.extend) (𝓝[>] (0:ℝ)) (𝓝 A) ∧
            (∀ t ∈ Ioo (0:ℝ) (1/2),
              F (γ.extend t) = A +
                ∫ u in Ioc (0:ℝ) t,
                  curveIntegralFun (NLS.ComplexAnalysis.holomorphicOneForm f) γ u) ∧
            (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm f z) = F b - A := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  obtain ⟨ε,hε,hconnector⟩ :=
    exists_sourceCriticalRootRatio_curvedEndpointConnector_curveIntegrable
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro c hc b γ hγ hupper hb hnear hlinear F hF
  have hdom (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
      (ne_of_gt (hupper t ht))
  have hint : CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) γ :=
    hconnector c hc γ hγ hdom hnear hlinear
  exact NLS.ComplexAnalysis.exists_primitive_limit_along_integrable_path
    f F {z : ℂ | 0 < z.im} (fun z hz => hF z hz)
    γ hγ hupper hb hint

/-- The analogous pathwise primitive limit for a connector in the
lower half-plane. -/
theorem exists_sourceCriticalRootRatio_lowerCurvedConnector_primitive_limit
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
    ∃ ε : ℝ, 0 < ε ∧ ∀ c ∈ ({l,r} : Set ℂ),
      ∀ {b : ℂ} (γ : Path c b),
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
        (∀ t ∈ Ioo (0:ℝ) 1, (γ.extend t).im < 0) →
        b.im < 0 →
        (∀ t ∈ Ioo (0:ℝ) 1,
          0 < ‖c-γ.extend t‖ ∧ ‖c-γ.extend t‖ ≤ ε) →
        (∃ k : ℝ, 0 < k ∧ ∀ t ∈ Ioo (0:ℝ) 1,
          k*t ≤ ‖c-γ.extend t‖) →
        ∀ F : ℂ → ℂ,
          (∀ z : ℂ, z.im < 0 → HasDerivAt F (f z) z) →
          ∃ A : ℂ,
            Tendsto (F ∘ γ.extend) (𝓝[>] (0:ℝ)) (𝓝 A) ∧
            (∀ t ∈ Ioo (0:ℝ) (1/2),
              F (γ.extend t) = A +
                ∫ u in Ioc (0:ℝ) t,
                  curveIntegralFun (NLS.ComplexAnalysis.holomorphicOneForm f) γ u) ∧
            (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm f z) = F b - A := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  obtain ⟨ε,hε,hconnector⟩ :=
    exists_sourceCriticalRootRatio_curvedEndpointConnector_curveIntegrable
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro c hc b γ hγ hlower hb hnear hlinear F hF
  have hdom (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
      (ne_of_lt (hlower t ht))
  have hint : CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) γ :=
    hconnector c hc γ hγ hdom hnear hlinear
  exact NLS.ComplexAnalysis.exists_primitive_limit_along_integrable_path
    f F {z : ℂ | z.im < 0} (fun z hz => hF z hz)
    γ hγ hlower hb hint

end NLS.ZakharovShabat
