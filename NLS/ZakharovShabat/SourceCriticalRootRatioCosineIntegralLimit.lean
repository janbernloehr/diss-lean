import NLS.ZakharovShabat.SourceCriticalRootRatioVerticalLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated limits of cosine-parametrized gap integrals

The cosine parameter makes the endpoint singularity of the selected
standard root uniformly integrable. We use the transverse bound and
the pointwise side limit to pass the upper displaced integral to its
boundary value.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The cosine of an interior angle lies strictly inside the signed
gap parameter interval. -/
theorem cos_mem_gapInterior {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    Real.cos θ ∈ Ioo (-1 : ℝ) 1 := by
  have hleft : Real.cos Real.pi < Real.cos θ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
  have hright : Real.cos θ < Real.cos 0 :=
    Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2.le hθ.1
  simpa using And.intro hleft hright

/-- Along positive vertical translates, the cosine-parametrized
critical-root quotient integral tends to the upper boundary integral. -/
theorem sourceCriticalRootRatio_upper_cosineIntegral_tendsto
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    Tendsto
      (fun y : ℝ => ∫ θ in (0:ℝ)..Real.pi,
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I) /
          sourceCanonicalRoot hp hp1 ψ
            (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I)) *
          (sourceStandardRootHalfGap hp hp1 ψ n * (Real.sin θ:ℂ)))
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (∫ θ in (0:ℝ)..Real.pi,
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)) /
          sourceCanonicalRootGapUpperValue hp hp1 ψ n (Real.cos θ)) *
          (sourceStandardRootHalfGap hp hp1 ψ n * (Real.sin θ:ℂ)))) := by
  let d : ℝ := ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re -
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)/2
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hδ : δ = (d:ℂ) :=
    sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 ψ hreal n
  obtain ⟨ε,M,hε,hM,hbound⟩ :=
    exists_sourceCriticalRootRatio_transverse_weighted_bound
      hp hp1 ψ hreal n hopen
  have hsmall0 : ∀ᶠ y in 𝓝 (0:ℝ), y < ε := Iio_mem_nhds hε
  have hsmall : ∀ᶠ y in 𝓝[Set.Ioi 0] (0:ℝ), y < ε :=
    hsmall0.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ y in 𝓝[Set.Ioi 0] (0:ℝ), 0 < y :=
    self_mem_nhdsWithin
  have hweight : Continuous (fun θ : ℝ => δ * (Real.sin θ:ℂ)) := by
    fun_prop
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => M)
  · filter_upwards [hpos] with y hy
    exact (((sourceCriticalRootRatio_vertical_continuous
      hp hp1 ψ hreal n y hy.ne').comp Real.continuous_cos).mul
      hweight).aestronglyMeasurable
  · filter_upwards [hpos,hsmall] with y hy hyε
    refine Filter.Eventually.of_forall ?_
    intro θ hθ
    have hθoc : θ ∈ Ioc 0 Real.pi := by
      simpa [uIoc_of_le (le_of_lt Real.pi_pos)] using hθ
    have hθcc : θ ∈ Icc 0 Real.pi := ⟨hθoc.1.le,hθoc.2⟩
    have hcos : Real.cos θ ∈ Icc (-1 : ℝ) 1 := Real.cos_mem_Icc θ
    have hwt : δ*(Real.sin θ:ℂ) =
        ((d*Real.sqrt (1-Real.cos θ^2):ℝ):ℂ) := by
      rw [hδ, Real.sin_eq_sqrt_one_sub_cos_sq hθcc.1 hθcc.2]
      norm_cast
    rw [hwt]
    exact hbound (Real.cos θ) hcos y hy.ne'
      (by rw [abs_of_pos hy]; exact hyε.le)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall ?_
    intro θ hθ
    have hθoc : θ ∈ Ioc (0:ℝ) Real.pi := by
      simpa [uIoc_of_le (le_of_lt Real.pi_pos)] using hθ
    by_cases hπ : θ = Real.pi
    · subst θ
      simp
    · have hθint : θ ∈ Ioo 0 Real.pi :=
        ⟨hθoc.1,lt_of_le_of_ne hθoc.2 hπ⟩
      exact (sourceCriticalRootRatio_tendsto_vertical_upper
        hp hp1 ψ hreal n hopen (Real.cos θ)
        (cos_mem_gapInterior hθint)).mul tendsto_const_nhds

/-- The analogous cosine integral converges to the lower boundary
value along negative vertical translates. -/
theorem sourceCriticalRootRatio_lower_cosineIntegral_tendsto
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    Tendsto
      (fun y : ℝ => ∫ θ in (0:ℝ)..Real.pi,
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I) /
          sourceCanonicalRoot hp hp1 ψ
            (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I)) *
          (sourceStandardRootHalfGap hp hp1 ψ n * (Real.sin θ:ℂ)))
      (𝓝[Set.Iio 0] (0:ℝ))
      (𝓝 (∫ θ in (0:ℝ)..Real.pi,
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)) /
          sourceCanonicalRootGapLowerValue hp hp1 ψ n (Real.cos θ)) *
          (sourceStandardRootHalfGap hp hp1 ψ n * (Real.sin θ:ℂ)))) := by
  let d : ℝ := ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re -
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)/2
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hδ : δ = (d:ℂ) :=
    sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 ψ hreal n
  obtain ⟨ε,M,hε,hM,hbound⟩ :=
    exists_sourceCriticalRootRatio_transverse_weighted_bound
      hp hp1 ψ hreal n hopen
  have hsmall0 : ∀ᶠ y in 𝓝 (0:ℝ), -ε < y :=
    Ioi_mem_nhds (neg_lt_zero.mpr hε)
  have hsmall : ∀ᶠ y in 𝓝[Set.Iio 0] (0:ℝ), -ε < y :=
    hsmall0.filter_mono nhdsWithin_le_nhds
  have hneg : ∀ᶠ y in 𝓝[Set.Iio 0] (0:ℝ), y < 0 :=
    self_mem_nhdsWithin
  have hweight : Continuous (fun θ : ℝ => δ * (Real.sin θ:ℂ)) := by
    fun_prop
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => M)
  · filter_upwards [hneg] with y hy
    exact (((sourceCriticalRootRatio_vertical_continuous
      hp hp1 ψ hreal n y hy.ne).comp Real.continuous_cos).mul
      hweight).aestronglyMeasurable
  · filter_upwards [hneg,hsmall] with y hy hyε
    refine Filter.Eventually.of_forall ?_
    intro θ hθ
    have hθoc : θ ∈ Ioc 0 Real.pi := by
      simpa [uIoc_of_le (le_of_lt Real.pi_pos)] using hθ
    have hθcc : θ ∈ Icc 0 Real.pi := ⟨hθoc.1.le,hθoc.2⟩
    have hcos : Real.cos θ ∈ Icc (-1 : ℝ) 1 := Real.cos_mem_Icc θ
    have hwt : δ*(Real.sin θ:ℂ) =
        ((d*Real.sqrt (1-Real.cos θ^2):ℝ):ℂ) := by
      rw [hδ, Real.sin_eq_sqrt_one_sub_cos_sq hθcc.1 hθcc.2]
      norm_cast
    rw [hwt]
    exact hbound (Real.cos θ) hcos y hy.ne
      (by rw [abs_of_neg hy]; linarith)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall ?_
    intro θ hθ
    have hθoc : θ ∈ Ioc (0:ℝ) Real.pi := by
      simpa [uIoc_of_le (le_of_lt Real.pi_pos)] using hθ
    by_cases hπ : θ = Real.pi
    · subst θ
      simp
    · have hθint : θ ∈ Ioo 0 Real.pi :=
        ⟨hθoc.1,lt_of_le_of_ne hθoc.2 hπ⟩
      exact (sourceCriticalRootRatio_tendsto_vertical_lower
        hp hp1 ψ hreal n hopen (Real.cos θ)
        (cos_mem_gapInterior hθint)).mul tendsto_const_nhds

end NLS.ZakharovShabat
