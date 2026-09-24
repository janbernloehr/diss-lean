import NLS.ZakharovShabat.SourceCriticalRootRatioGapSideIntegral

/-!
# Regularity and truncation of the critical-root gap-side integrals

The deleted critical-root factor is analytic across the selected gap.
Its product with the selected critical factor is therefore continuous
on the entire closed gap, including its branch-point endpoints. This
makes the straight side integrals genuine interval integrals and shows
that deleting both endpoints tends to their proved zero value.
-/

noncomputable section
open Set Complex Filter MeasureTheory
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The selected regular numerator is continuous even at both gap
endpoints of a real-type source potential. -/
theorem sourceCriticalRootGapNumerator_continuousOn
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    ContinuousOn (sourceCriticalRootGapNumerator hp hp1 ψ n)
      (standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)) := by
  obtain ⟨W₁,_,_,hreal₁,hpoint⟩ :=
    exists_global_source_gapPoint_mem_omittedDomain hp hp1
  obtain ⟨W₂,_,hreal₂,hext⟩ :=
    exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  have hψ₁ : ψ ∈ W₁ := hreal₁ hreal
  have hψ₂ : ψ ∈ W₂ := hreal₂ hreal
  intro z hz
  obtain ⟨t,ht,rfl⟩ := hz
  have hdom := hpoint ψ hψ₁ n t ht.1 ht.2
  have hcont : ContinuousAt (sourceCriticalRootRatioExtension hp hp1 n ψ)
      (sourceCanonicalRootGapPoint hp hp1 ψ n t) :=
    (hext ψ hψ₂ n _ hdom).continuousAt
  change ContinuousWithinAt
    (fun w : ℂ =>
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n-w) *
        sourceCriticalRootRatioExtension hp hp1 n ψ w)
    (standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n))
    (sourceCanonicalRootGapPoint hp hp1 ψ n t)
  exact ((continuousAt_const.sub continuousAt_id).mul hcont).continuousWithinAt

/-- The half-gap Jacobian is nonzero for an open real gap. -/
theorem sourceStandardRootHalfGap_ne_zero_of_openRealGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    sourceStandardRootHalfGap hp hp1 ψ n ≠ 0 := by
  rw [sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 ψ hreal n]
  have hpos : 0 <
      ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re -
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re)/2 := by
    linarith
  exact_mod_cast hpos.ne'

/-- The singular-looking pullback along either straight gap side is
interval integrable through both branch-point endpoints. -/
theorem sourceCriticalRoot_gapSidePathIntegrand_intervalIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (upper : Bool) :
    IntervalIntegrable
      (fun t : ℝ =>
        sourceCriticalRootGapNumerator hp hp1 ψ n
          (sourceCanonicalRootGapPoint hp hp1 ψ n t) *
        (sourceStandardRootHalfGap hp hp1 ψ n /
          ((if upper then -sourceStandardRootHalfGap hp hp1 ψ n*I
            else sourceStandardRootHalfGap hp hp1 ψ n*I) *
            (Real.sqrt (1-t^2):ℂ)))) volume (-1) 1 := by
  exact gapSidePathIntegrand_intervalIntegrable
    (sourceStandardRootMidpoint hp hp1 ψ n)
    (sourceStandardRootHalfGap hp hp1 ψ n)
    (sourceCriticalRootGapNumerator hp hp1 ψ n)
    (sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen)
    (sourceCriticalRootGapNumerator_continuousOn hp hp1 ψ hreal n)
    (-1) 1 (by norm_num) (by norm_num) upper

/-- Doubly truncated straight side integrals converge to zero as the
cutoffs at both branch points vanish. -/
theorem sourceCriticalRoot_gapSidePathIntegral_double_trunc_tendsto_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (upper : Bool) :
    Tendsto (fun ε : ℝ =>
      gapSidePathIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)
        (sourceCriticalRootGapNumerator hp hp1 ψ n)
        (-1+ε) (1-ε) upper)
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let F := sourceCriticalRootGapNumerator hp hp1 ψ n
  have hδ : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hF : ContinuousOn F (standardRootGapSegment τ δ) :=
    sourceCriticalRootGapNumerator_continuousOn hp hp1 ψ hreal n
  have hlim := gapSidePathIntegral_double_trunc_tendsto τ δ F hδ hF upper
  have hident := gapSidePathIntegral_eq_boundary τ δ F 1 hδ
    (by norm_num) (by norm_num) upper
  have hzero := sourceCriticalRoot_gapSidePathIntegral_eq_zero
    hp hp1 ψ hreal n hopen upper
  rw [← hident, hzero] at hlim
  exact hlim

end NLS.ZakharovShabat
