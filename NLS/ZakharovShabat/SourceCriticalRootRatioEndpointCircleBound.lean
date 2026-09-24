import NLS.ZakharovShabat.SourceStandardRootEndpointCircleBound

/-!
# Weighted quotient bounds on small circles around gap endpoints

The regular numerator stays bounded near a real periodic gap. Combined
with the endpoint-circle lower bound for the selected standard root,
this controls the full quotient by the inverse square root of the arc
radius wherever the arc avoids all periodic gaps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common small radius and bound work on circles around both
endpoints of an open real-type gap. -/
theorem exists_sourceCriticalRootRatio_endpointCircle_weighted_bound
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
      ∀ ρ ∈ Ioc 0 ε, ∀ c ∈ ({l,r} : Set ℂ), ∀ z : ℂ,
        z ∈ sourceCanonicalRootDomain hp hp1 ψ →
        ‖c-z‖ = ρ →
        ‖(deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
            sourceCanonicalRoot hp hp1 ψ z) *
          ((Real.sqrt (((r.re-l.re)/2)*ρ) : ℝ) : ℂ)‖ ≤ M := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let S := standardRootGapSegment
    (sourceStandardRootMidpoint hp hp1 ψ n)
    (sourceStandardRootHalfGap hp hp1 ψ n)
  obtain ⟨ε₀,M,hε₀,hM,_,hFbound⟩ :=
    exists_sourceCriticalRootGap_thickening_regularNumerator_bound
      hp hp1 ψ hreal n
  let ε := min ε₀ ((r.re-l.re)/2)
  have hgap : 0 < (r.re-l.re)/2 := by
    have h := hopen
    change l.re < r.re at h
    linarith
  have hε : 0 < ε := lt_min hε₀ hgap
  refine ⟨ε,M,hε,hM,?_⟩
  intro ρ hρ c hc z hz hdist
  have hcS : c ∈ S := by
    simp only [mem_insert_iff, mem_singleton_iff] at hc
    rcases hc with h | h
    · subst c
      have hq : sourceCanonicalRootGapPoint hp hp1 ψ n (-1) ∈ S :=
        ⟨-1,by norm_num,rfl⟩
      simpa only [sourceCanonicalRootGapPoint_neg_one_eq_left] using hq
    · subst c
      have hq : sourceCanonicalRootGapPoint hp hp1 ψ n 1 ∈ S :=
        ⟨1,by norm_num,rfl⟩
      simpa only [sourceCanonicalRootGapPoint_one_eq_right] using hq
  have hzK : z ∈ cthickening ε₀ S :=
    Metric.mem_cthickening_of_dist_le z c ε₀ S hcS (by
      rw [dist_eq_norm,norm_sub_rev,hdist]
      exact hρ.2.trans (min_le_left _ _))
  have hF : ‖sourceCriticalRootGapNumerator hp hp1 ψ n z‖ ≤ M :=
    hFbound z hzK
  have hρsmall : ρ ≤ (r.re-l.re)/2 :=
    hρ.2.trans (min_le_right _ _)
  have hroot : Real.sqrt (((r.re-l.re)/2)*ρ) ≤
      ‖sourceStandardRoot hp hp1 ψ n z‖ := by
    simp only [mem_insert_iff, mem_singleton_iff] at hc
    rcases hc with h | h
    · subst c
      exact sourceStandardRoot_leftEndpoint_circle_norm_lower_bound
        hp hp1 ψ n hopen ρ hρ.1.le hρsmall z (hz n) hdist
    · subst c
      exact sourceStandardRoot_rightEndpoint_circle_norm_lower_bound
        hp hp1 ψ n hopen ρ hρ.1.le hρsmall z (hz n) hdist
  have hB : sourceStandardRoot hp hp1 ψ n z ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hz n)
  have hfactor :
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z =
        sourceCriticalRootGapNumerator hp hp1 ψ n z /
          sourceStandardRoot hp hp1 ψ n z := by
    rw [sourceCriticalRootRatio_eq_selectedFactor_mul_extension
      hp hp1 ψ n z hz]
    unfold sourceCriticalRootGapNumerator
    simp only [div_eq_mul_inv]
    ring
  rw [hfactor]
  exact norm_div_mul_real_le_of_weight_le_norm _ _
    (Real.sqrt (((r.re-l.re)/2)*ρ)) M
    (Real.sqrt_nonneg _) hM.le hF hroot hB

end NLS.ZakharovShabat
