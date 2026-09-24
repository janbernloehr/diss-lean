import NLS.ComplexAnalysis.InverseSqrtIntegral
import NLS.ZakharovShabat.SourceCriticalRootRatioConnectorBound

/-!
# Integrability of the quotient on open-gap endpoint connectors

The square-root endpoint bound makes the critical-root quotient
integrable along both short upward vertical connectors, even though
the quotient itself need not extend continuously to their endpoints.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At both endpoints of an open real-type gap, the critical-root
quotient is integrable along a sufficiently short upward connector. -/
theorem exists_sourceCriticalRootRatio_upperEndpointConnector_integrable
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ ({(-1 : ℝ), 1} : Set ℝ),
        IntegrableOn
          (fun y : ℝ =>
            deriv (canonicalDiscriminant hp (periodOnePotential ψ))
                (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I) /
              sourceCanonicalRoot hp hp1 ψ
                (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I))
          (Ioo 0 ε) := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  have hd : 0 < b-a := sub_pos.2 hopen
  obtain ⟨ε, M, hε, _, hbound⟩ :=
    exists_sourceCriticalRootRatio_endpointConnector_weighted_bound
      hp hp1 ψ hreal n hopen
  refine ⟨ε, hε, ?_⟩
  intro t ht
  let z (y : ℝ) : ℂ := sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I
  let f (y : ℝ) : ℂ :=
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (z y) /
      sourceCanonicalRoot hp hp1 ψ (z y)
  have hpath : Continuous z := by
    unfold z
    fun_prop
  have hcont : ContinuousOn f (Ioo (0:ℝ) ε) := by
    intro y hy
    have hz : z y ∈ sourceCanonicalRootDomain hp hp1 ψ :=
      sourceCanonicalRootGapPoint_vertical_mem_domain_of_realType
        hp hp1 ψ hreal n t y (ne_of_gt hy.1)
    exact ((sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ _ hz).continuousAt.comp
      hpath.continuousAt).continuousWithinAt
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioo 0 ε)) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  apply NLS.ComplexAnalysis.integrableOn_Ioo_of_norm_mul_sqrt_mul_le hd hε hfm
  intro y hy
  simpa only [f, z, a, b, abs_of_pos hy.1] using
    hbound t ht y (ne_of_gt hy.1)
      (by simpa [abs_of_pos hy.1] using hy.2.le)

/-- The same local integrability holds below both open-gap endpoints,
using positive `y` to parametrize the downward distance. -/
theorem exists_sourceCriticalRootRatio_lowerEndpointConnector_integrable
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ ({(-1 : ℝ), 1} : Set ℝ),
        IntegrableOn
          (fun y : ℝ =>
            deriv (canonicalDiscriminant hp (periodOnePotential ψ))
                (sourceCanonicalRootGapPoint hp hp1 ψ n t + ((-y:ℝ):ℂ)*I) /
              sourceCanonicalRoot hp hp1 ψ
                (sourceCanonicalRootGapPoint hp hp1 ψ n t + ((-y:ℝ):ℂ)*I))
          (Ioo 0 ε) := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  have hd : 0 < b-a := sub_pos.2 hopen
  obtain ⟨ε, M, hε, _, hbound⟩ :=
    exists_sourceCriticalRootRatio_endpointConnector_weighted_bound
      hp hp1 ψ hreal n hopen
  refine ⟨ε, hε, ?_⟩
  intro t ht
  let z (y : ℝ) : ℂ := sourceCanonicalRootGapPoint hp hp1 ψ n t + ((-y:ℝ):ℂ)*I
  let f (y : ℝ) : ℂ :=
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (z y) /
      sourceCanonicalRoot hp hp1 ψ (z y)
  have hpath : Continuous z := by
    unfold z
    fun_prop
  have hcont : ContinuousOn f (Ioo (0:ℝ) ε) := by
    intro y hy
    have hz : z y ∈ sourceCanonicalRootDomain hp hp1 ψ :=
      sourceCanonicalRootGapPoint_vertical_mem_domain_of_realType
        hp hp1 ψ hreal n t (-y) (neg_ne_zero.2 (ne_of_gt hy.1))
    exact ((sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ _ hz).continuousAt.comp
      hpath.continuousAt).continuousWithinAt
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioo 0 ε)) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  apply NLS.ComplexAnalysis.integrableOn_Ioo_of_norm_mul_sqrt_mul_le hd hε hfm
  intro y hy
  simpa only [f, z, a, b, abs_neg, abs_of_pos hy.1] using
    hbound t ht (-y) (neg_ne_zero.2 (ne_of_gt hy.1))
      (by simpa [abs_of_pos hy.1] using hy.2.le)

end NLS.ZakharovShabat
