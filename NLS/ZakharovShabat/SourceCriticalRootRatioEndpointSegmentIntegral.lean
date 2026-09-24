import NLS.ComplexAnalysis.VerticalSegmentIntegral
import NLS.ZakharovShabat.SourceCriticalRootRatioEndpointConnectorIntegrable

/-!
# Actual curve integrals on singular endpoint segments

At an open real-type gap, short vertical segments starting at either
branch point have well-defined curve integrals. Their integrals vanish
as the segment length shrinks, on both sides of the real axis.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Short upward segments starting at either open-gap endpoint are
genuinely curve-integrable despite the branch-point singularity. -/
theorem exists_sourceCriticalRootRatio_upperEndpointSegment_curveIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ ({(-1 : ℝ), 1} : Set ℝ),
        ∀ y ∈ Ioo (0:ℝ) ε,
          CurveIntegrable
            (NLS.ComplexAnalysis.holomorphicOneForm
              (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
                sourceCanonicalRoot hp hp1 ψ w))
            (Path.segment (sourceCanonicalRootGapPoint hp hp1 ψ n t)
              (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*Complex.I)) := by
  obtain ⟨ε, hε, hint⟩ :=
    exists_sourceCriticalRootRatio_upperEndpointConnector_integrable
      hp hp1 ψ hreal n hopen
  refine ⟨ε, hε, ?_⟩
  intro t ht y hy
  have hinty := (hint t ht).mono_set (Ioo_subset_Ioo le_rfl hy.2.le)
  have hintInterval := (intervalIntegrable_iff_integrableOn_Ioo_of_le hy.1.le).2 hinty
  exact NLS.ComplexAnalysis.curveIntegrable_verticalSegment_of_intervalIntegrable
    _ _ y hy.1 hintInterval

/-- The corresponding downward endpoint segments are also
curve-integrable. -/
theorem exists_sourceCriticalRootRatio_lowerEndpointSegment_curveIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ ({(-1 : ℝ), 1} : Set ℝ),
        ∀ y ∈ Ioo (0:ℝ) ε,
          CurveIntegrable
            (NLS.ComplexAnalysis.holomorphicOneForm
              (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
                sourceCanonicalRoot hp hp1 ψ w))
            (Path.segment (sourceCanonicalRootGapPoint hp hp1 ψ n t)
              (sourceCanonicalRootGapPoint hp hp1 ψ n t + ((-y:ℝ):ℂ)*Complex.I)) := by
  obtain ⟨ε, hε, hint⟩ :=
    exists_sourceCriticalRootRatio_lowerEndpointConnector_integrable
      hp hp1 ψ hreal n hopen
  refine ⟨ε, hε, ?_⟩
  intro t ht y hy
  have hinty := (hint t ht).mono_set (Ioo_subset_Ioo le_rfl hy.2.le)
  have hintInterval := (intervalIntegrable_iff_integrableOn_Ioo_of_le hy.1.le).2 hinty
  exact NLS.ComplexAnalysis.curveIntegrable_downwardSegment_of_intervalIntegrable
    _ _ y hy.1 hintInterval

/-- The integral along a short upward segment starting at either
open-gap endpoint tends to zero. -/
theorem sourceCriticalRootRatio_upperEndpointSegment_curveIntegral_tendsto_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (t : ℝ) (ht : t ∈ ({(-1 : ℝ), 1} : Set ℝ)) :
    Tendsto
      (fun y : ℝ => ∫ᶜ z in Path.segment
        (sourceCanonicalRootGapPoint hp hp1 ψ n t)
        (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*Complex.I),
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨ε, hε, hlim⟩ :=
    exists_sourceCriticalRootRatio_upperEndpointConnector_integral_tendsto_zero
      hp hp1 ψ hreal n hopen
  have hlim' := (hlim t ht).mul_const Complex.I
  have heq :
      (fun y : ℝ => ∫ᶜ z in Path.segment
        (sourceCanonicalRootGapPoint hp hp1 ψ n t)
        (sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*Complex.I),
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z) =ᶠ[𝓝[>] (0:ℝ)]
      (fun y : ℝ => (∫ v in Ioc 0 y,
        deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (sourceCanonicalRootGapPoint hp hp1 ψ n t + (v:ℂ)*Complex.I) /
          sourceCanonicalRoot hp hp1 ψ
            (sourceCanonicalRootGapPoint hp hp1 ψ n t + (v:ℂ)*Complex.I)) * Complex.I) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [NLS.ComplexAnalysis.curveIntegral_verticalSegment,
      intervalIntegral.integral_of_le hy.le]
  simpa using hlim'.congr' heq.symm

/-- The downward segments starting at the two open-gap endpoints
have the same shrinking zero limit. -/
theorem sourceCriticalRootRatio_lowerEndpointSegment_curveIntegral_tendsto_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (t : ℝ) (ht : t ∈ ({(-1 : ℝ), 1} : Set ℝ)) :
    Tendsto
      (fun y : ℝ => ∫ᶜ z in Path.segment
        (sourceCanonicalRootGapPoint hp hp1 ψ n t)
        (sourceCanonicalRootGapPoint hp hp1 ψ n t + ((-y:ℝ):ℂ)*Complex.I),
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨ε, hε, hlim⟩ :=
    exists_sourceCriticalRootRatio_lowerEndpointConnector_integral_tendsto_zero
      hp hp1 ψ hreal n hopen
  have hlim' := ((hlim t ht).mul_const Complex.I).neg
  have heq :
      (fun y : ℝ => ∫ᶜ z in Path.segment
        (sourceCanonicalRootGapPoint hp hp1 ψ n t)
        (sourceCanonicalRootGapPoint hp hp1 ψ n t + ((-y:ℝ):ℂ)*Complex.I),
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z) =ᶠ[𝓝[>] (0:ℝ)]
      (fun y : ℝ => -((∫ v in Ioc 0 y,
        deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (sourceCanonicalRootGapPoint hp hp1 ψ n t + ((-v:ℝ):ℂ)*Complex.I) /
          sourceCanonicalRoot hp hp1 ψ
            (sourceCanonicalRootGapPoint hp hp1 ψ n t + ((-v:ℝ):ℂ)*Complex.I)) * Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [NLS.ComplexAnalysis.curveIntegral_downwardSegment,
      intervalIntegral.integral_of_le hy.le]
  simpa using hlim'.congr' heq.symm

end NLS.ZakharovShabat
