import NLS.ZakharovShabat.SourceCriticalRootRatioCosineIntegralLimit

/-!
# Vanishing cosine boundary integrals of the critical-root quotient

The explicit upper and lower canonical-root boundary quotients agree
with the side kernels already integrated in Lemma 10.11. The cosine
boundary integrals therefore vanish on every open real-type gap.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The upper canonical-root boundary quotient has zero cosine-path
integral over an open real-type gap. -/
theorem sourceCriticalRootRatio_upper_cosineBoundaryIntegral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (∫ θ in (0:ℝ)..Real.pi,
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)) /
        sourceCanonicalRootGapUpperValue hp hp1 ψ n (Real.cos θ)) *
        (sourceStandardRootHalfGap hp hp1 ψ n * (Real.sin θ:ℂ))) = 0 := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let F := sourceCriticalRootGapNumerator hp hp1 ψ n
  have hδ : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hgap := sourceCanonicalPeriodicGap_ne_zero_of_openRealGap
    hp hp1 ψ hreal n hopen
  have hdom (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
      sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
        sourceStandardRootOmittedDomain hp hp1 ψ n :=
    sourceStandardRootGapSegment_subset_omittedDomain_of_realType
      hp hp1 ψ hreal n ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
  have hpoint (θ : ℝ) (hθ : θ ∈ Ioo 0 Real.pi) :
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)) /
        sourceCanonicalRootGapUpperValue hp hp1 ψ n (Real.cos θ)) *
          (δ*(Real.sin θ:ℂ)) =
      F (τ+δ*(Real.cos θ:ℂ)) *
        ((δ*(Real.sin θ:ℂ)) /
          (-δ*I*(Real.sqrt (1-(Real.cos θ)^2):ℂ))) := by
    have ht := cos_mem_gapInterior hθ
    have hf := discriminant_derivative_div_canonicalRootGapUpperValue_eq_selectedFactor
      hp hp1 ψ n (Real.cos θ) hgap ht (hdom _ ht)
    change deriv (canonicalDiscriminant hp (periodOnePotential ψ))
        (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)) /
          sourceCanonicalRootGapUpperValue hp hp1 ψ n (Real.cos θ) =
      F (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)) /
        (-δ*I*(Real.sqrt (1-(Real.cos θ)^2):ℂ)) at hf
    rw [hf]
    change (F (τ+δ*(Real.cos θ:ℂ)) /
        (-δ*I*(Real.sqrt (1-(Real.cos θ)^2):ℂ))) *
        (δ*(Real.sin θ:ℂ)) = _
    simp only [div_eq_mul_inv]
    ring
  have heq : (∫ θ in (0:ℝ)..Real.pi,
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)) /
        sourceCanonicalRootGapUpperValue hp hp1 ψ n (Real.cos θ)) *
          (δ*(Real.sin θ:ℂ))) =
      gapSideBoundaryIntegral τ δ F 1 true := by
    unfold gapSideBoundaryIntegral
    simp only [Real.arccos_one, ite_true]
    apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
    intro θ hθ
    exact hpoint θ hθ
  rw [heq, ← gapSidePathIntegral_eq_boundary τ δ F 1 hδ
    (by norm_num) (by norm_num) true]
  exact sourceCriticalRoot_gapSidePathIntegral_eq_zero
    hp hp1 ψ hreal n hopen true

/-- The lower canonical-root boundary quotient has zero cosine-path
integral over an open real-type gap. -/
theorem sourceCriticalRootRatio_lower_cosineBoundaryIntegral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (∫ θ in (0:ℝ)..Real.pi,
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)) /
        sourceCanonicalRootGapLowerValue hp hp1 ψ n (Real.cos θ)) *
        (sourceStandardRootHalfGap hp hp1 ψ n * (Real.sin θ:ℂ))) = 0 := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let F := sourceCriticalRootGapNumerator hp hp1 ψ n
  have hδ : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hgap := sourceCanonicalPeriodicGap_ne_zero_of_openRealGap
    hp hp1 ψ hreal n hopen
  have hdom (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
      sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
        sourceStandardRootOmittedDomain hp hp1 ψ n :=
    sourceStandardRootGapSegment_subset_omittedDomain_of_realType
      hp hp1 ψ hreal n ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
  have hpoint (θ : ℝ) (hθ : θ ∈ Ioo 0 Real.pi) :
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)) /
        sourceCanonicalRootGapLowerValue hp hp1 ψ n (Real.cos θ)) *
          (δ*(Real.sin θ:ℂ)) =
      F (τ+δ*(Real.cos θ:ℂ)) *
        ((δ*(Real.sin θ:ℂ)) /
          (δ*I*(Real.sqrt (1-(Real.cos θ)^2):ℂ))) := by
    have ht := cos_mem_gapInterior hθ
    have hf := discriminant_derivative_div_canonicalRootGapLowerValue_eq_selectedFactor
      hp hp1 ψ n (Real.cos θ) hgap ht (hdom _ ht)
    change deriv (canonicalDiscriminant hp (periodOnePotential ψ))
        (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)) /
          sourceCanonicalRootGapLowerValue hp hp1 ψ n (Real.cos θ) =
      F (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)) /
        (δ*I*(Real.sqrt (1-(Real.cos θ)^2):ℂ)) at hf
    rw [hf]
    change (F (τ+δ*(Real.cos θ:ℂ)) /
        (δ*I*(Real.sqrt (1-(Real.cos θ)^2):ℂ))) *
        (δ*(Real.sin θ:ℂ)) = _
    simp only [div_eq_mul_inv]
    ring
  have heq : (∫ θ in (0:ℝ)..Real.pi,
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)) /
        sourceCanonicalRootGapLowerValue hp hp1 ψ n (Real.cos θ)) *
          (δ*(Real.sin θ:ℂ))) =
      gapSideBoundaryIntegral τ δ F 1 false := by
    unfold gapSideBoundaryIntegral
    simp only [Real.arccos_one, Bool.false_eq_true, ite_false]
    apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
    intro θ hθ
    exact hpoint θ hθ
  rw [heq, ← gapSidePathIntegral_eq_boundary τ δ F 1 hδ
    (by norm_num) (by norm_num) false]
  exact sourceCriticalRoot_gapSidePathIntegral_eq_zero
    hp hp1 ψ hreal n hopen false

/-- The upper vertically displaced cosine integral tends to zero as
the displacement shrinks to the real gap. -/
theorem sourceCriticalRootRatio_upper_cosineIntegral_tendsto_zero
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
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
  simpa only [sourceCriticalRootRatio_upper_cosineBoundaryIntegral_eq_zero
    hp hp1 ψ hreal n hopen] using
    sourceCriticalRootRatio_upper_cosineIntegral_tendsto
      hp hp1 ψ hreal n hopen

/-- The lower vertically displaced cosine integral has the same zero
limit. -/
theorem sourceCriticalRootRatio_lower_cosineIntegral_tendsto_zero
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
      (𝓝[Set.Iio 0] (0:ℝ)) (𝓝 0) := by
  simpa only [sourceCriticalRootRatio_lower_cosineBoundaryIntegral_eq_zero
    hp hp1 ψ hreal n hopen] using
    sourceCriticalRootRatio_lower_cosineIntegral_tendsto
      hp hp1 ψ hreal n hopen

end NLS.ZakharovShabat
