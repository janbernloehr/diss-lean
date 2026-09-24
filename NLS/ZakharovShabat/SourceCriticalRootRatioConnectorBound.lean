import NLS.ZakharovShabat.SourceStandardRootVerticalEndpointBound

/-!
# Weighted critical-root quotient bound on gap endpoint connectors

The selected standard root is the only singular factor near an open
real-type gap. Multiplying the full quotient by the square root of the
vertical distance cancels its endpoint growth uniformly on either
short vertical connector.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full critical-root quotient has a square-root weighted bound
on both endpoint vertical lines in a uniform gap neighborhood. -/
theorem exists_sourceCriticalRootRatio_endpointConnector_weighted_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ t ∈ ({(-1 : ℝ), 1} : Set ℝ), ∀ y : ℝ,
        y ≠ 0 → |y| ≤ ε →
          let z := sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I
          ‖(deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
              sourceCanonicalRoot hp hp1 ψ z) *
            ((Real.sqrt ((b-a)*|y|) : ℝ) : ℂ)‖ ≤ M := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let S := standardRootGapSegment
    (sourceStandardRootMidpoint hp hp1 ψ n)
    (sourceStandardRootHalfGap hp hp1 ψ n)
  obtain ⟨ε,M,hε,hM,hKdom,hFbound⟩ :=
    exists_sourceCriticalRootGap_thickening_regularNumerator_bound
      hp hp1 ψ hreal n
  refine ⟨ε,M,hε,hM,?_⟩
  intro t ht y hy hyε
  let q := sourceCanonicalRootGapPoint hp hp1 ψ n t
  let z := q + (y:ℂ)*I
  let w : ℝ := Real.sqrt ((b-a)*|y|)
  have htc : t ∈ Icc (-1 : ℝ) 1 := by
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with h | h
    · subst t
      norm_num
    · subst t
      norm_num
  have hqS : q ∈ S := ⟨t,htc,rfl⟩
  have hdist : dist z q = |y| := by
    calc
      dist z q = ‖(y:ℂ)*I‖ := by
        rw [dist_eq_norm]
        congr 1
        dsimp [z]
        ring
      _ = |y| := by simp
  have hzK : z ∈ cthickening ε S :=
    Metric.mem_cthickening_of_dist_le z q ε S hqS
      (by simpa [hdist] using hyε)
  have hzfull : z ∈ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootGapPoint_vertical_mem_domain_of_realType
      hp hp1 ψ hreal n t y hy
  have hF : ‖sourceCriticalRootGapNumerator hp hp1 ψ n z‖ ≤ M :=
    hFbound z hzK
  have hroot : w ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ := by
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with h | h
    · subst t
      simpa [z,q,sourceCanonicalRootGapPoint_neg_one_eq_left,w,a,b] using
        sourceStandardRoot_leftEndpoint_vertical_norm_lower_bound
          hp hp1 ψ hreal n hopen y hy
    · subst t
      simpa [z,q,sourceCanonicalRootGapPoint_one_eq_right,w,a,b] using
        sourceStandardRoot_rightEndpoint_vertical_norm_lower_bound
          hp hp1 ψ hreal n hopen y hy
  have hB : sourceStandardRoot hp hp1 ψ n z ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hzfull n)
  have hfactor :
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z =
        sourceCriticalRootGapNumerator hp hp1 ψ n z /
          sourceStandardRoot hp hp1 ψ n z := by
    rw [sourceCriticalRootRatio_eq_selectedFactor_mul_extension
      hp hp1 ψ n z hzfull]
    unfold sourceCriticalRootGapNumerator
    simp only [div_eq_mul_inv]
    ring
  dsimp only
  rw [hfactor]
  exact norm_div_mul_real_le_of_weight_le_norm _ _ w M
    (Real.sqrt_nonneg _) hM.le hF hroot hB

end NLS.ZakharovShabat
