import NLS.ZakharovShabat.NormalizedActionFactorBound
import NLS.ZakharovShabat.SourceNormalizedActionFactorContinuity
import NLS.ZakharovShabat.SourceStandardRootWeightedRealCircleBoundary
import NLS.ZakharovShabat.SourceCriticalRootRatioSourceAnalytic
import Mathlib.Topology.ContinuousMap.Compact

/-! # Equation (5.15) on the real source locus, including collapsed gaps -/
noncomputable section
open Complex Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complementary spectral factor as a continuous function on the entire closed gap.
The phase has norm one, so its supremum norm is the χ norm used in Section 28. -/
def sourceRealGapFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    C(Icc (-1:ℝ) 1,ℂ) where
  toFun t := I*sourceCriticalRootRatioExtension hp hp1 n ψ
    (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t.val:ℂ))
  continuous_toFun := by
    obtain ⟨W₁,_,_,hreal₁,hpoint⟩ := exists_global_source_gapPoint_mem_omittedDomain hp hp1
    obtain ⟨W₂,_,hreal₂,hext⟩ := exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
    have hF : ContinuousOn (sourceCriticalRootRatioExtension hp hp1 n ψ)
        (standardRootGapSegment (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n)) := by
      intro z hz
      obtain ⟨t,ht,rfl⟩ := hz
      exact ((hext ψ (hreal₂ hreal) n _ (hpoint ψ (hreal₁ hreal) n t ht.1 ht.2)).continuousAt).continuousWithinAt
    apply continuous_const.mul
    apply hF.comp_continuous (by fun_prop)
    intro t
    exact ⟨t.val,t.property,rfl⟩

/-- The phase-normalized factor is the actual deleted critical-root product χ. -/
theorem sourceRealGapFactor_apply_eq_product (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (t : Icc (-1:ℝ) 1) :
    sourceRealGapFactor hp hp1 ψ hreal n t =
      sourceSingleRootQuotientJointProduct hp hp1 n
        (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t.val:ℂ),
          (canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ),ψ)) := by
  change I*(-I*_) = _
  simp [← mul_assoc]

/-- The continuous-function norm is exactly a uniform bound over the original closed gap. -/
theorem sourceRealGapFactor_norm_le_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (K : ℝ) (hK : 0 ≤ K) :
    ‖sourceRealGapFactor hp hp1 ψ hreal n‖ ≤ K ↔
      ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n, ‖sourceCriticalRootRatioExtension hp hp1 n ψ z‖ ≤ K := by
  rw [(sourceRealGapFactor hp hp1 ψ hreal n).norm_le hK]
  constructor
  · intro h z hz
    rw [← sourceStandardRoot_gapSegment_eq_periodicSegment] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    have hh := h ⟨t,ht⟩
    change ‖I*sourceCriticalRootRatioExtension hp hp1 n ψ _‖ ≤ K at hh
    simpa only [norm_mul,Complex.norm_I,one_mul] using hh
  · intro h t
    have hz : sourceStandardRootMidpoint hp hp1 ψ n+
        sourceStandardRootHalfGap hp hp1 ψ n*(t.val:ℂ) ∈ sourcePeriodicSegment hp hp1 ψ n := by
      rw [← sourceStandardRoot_gapSegment_eq_periodicSegment]
      exact ⟨t.val,t.property,rfl⟩
    change ‖I*sourceCriticalRootRatioExtension hp hp1 n ψ _‖ ≤ K
    simpa only [norm_mul,Complex.norm_I,one_mul] using h _ hz

/-- The critical offset has norm at most one on every noncollapsed real gap. -/
theorem source_real_critical_normalized_offset_le_one (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n ≠ 0) :
    ‖(canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        sourceStandardRootMidpoint hp hp1 ψ n)/sourceStandardRootHalfGap hp hp1 ψ n‖ ≤ 1 := by
  have hcrit := sourceCanonicalCriticalPoint_mem_periodicSegment_of_realType hp hp1 n ψ hreal
  rw [← sourceStandardRoot_gapSegment_eq_periodicSegment] at hcrit
  obtain ⟨t,ht,he⟩ := hcrit
  have hδ : sourceStandardRootHalfGap hp hp1 ψ n ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n
      (source_openRealGap_of_realType_gap_ne_zero hp hp1 n ψ hreal hgap)
  rw [← he,add_sub_cancel_left,mul_div_cancel_left₀ _ hδ,Complex.norm_real,Real.norm_eq_abs]
  exact abs_le.mpr ht

/-- The actual normalized action is bounded by three times the closed-gap factor norm. -/
theorem sourceRawNormalizedAction_le_three_gapFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n ≠ 0) :
    ‖4*sourceRawNormalizedAction hp hp1 n ψ‖ ≤ 3*‖sourceRealGapFactor hp hp1 ψ hreal n‖ := by
  rw [sourceRawNormalizedAction_eq_cosineModel_of_openRealGap hp hp1 ψ hreal n
    (source_openRealGap_of_realType_gap_ne_zero hp hp1 n ψ hreal hgap)]
  apply norm_normalizedActionCosineModel_le_three _ _
    (sourceCriticalRootRatioExtension_cosine_continuous hp hp1 ψ hreal n)
    _ (norm_nonneg _)
  · intro θ _
    exact ContinuousMap.norm_coe_le_norm (sourceRealGapFactor hp hp1 ψ hreal n)
      ⟨Real.cos θ,⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩⟩
  · exact source_real_critical_normalized_offset_le_one hp hp1 ψ hreal n hgap

/-- The division-free real action-gap bound is valid also when the gap collapses. -/
theorem sourceComplexAction_le_three_gapFactor_mul_gap_sq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    4*‖sourceComplexAction hp hp1 n ψ‖ ≤
      3*‖sourceRealGapFactor hp hp1 ψ hreal n‖*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := by
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · have hz := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 ψ hreal n).2.2.mpr hgap
    rw [sourceComplexAction_eq_sourceRealAction hp hp1 n ψ hreal,hz,hgap]
    simp
  · have h := sourceRawNormalizedAction_le_three_gapFactor hp hp1 ψ hreal n hgap
    simp only [sourceRawNormalizedAction,norm_mul,norm_div,norm_pow,Complex.norm_ofNat] at h
    have hpos : 0 < ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hgap)
    rw [← mul_div_assoc] at h
    exact (div_le_iff₀ hpos).mp h

/-- The factor-nine estimate (5.15), on all real sources, in a form retaining collapsed gaps. -/
theorem sourceComplexAction_le_nine_gapFactor_mul_gap_sq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    4*‖sourceComplexAction hp hp1 n ψ‖ ≤
      9*‖sourceRealGapFactor hp hp1 ψ hreal n‖*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := by
  have h := sourceComplexAction_le_three_gapFactor_mul_gap_sq hp hp1 ψ hreal n
  nlinarith [mul_nonneg (norm_nonneg (sourceRealGapFactor hp hp1 ψ hreal n))
    (sq_nonneg ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖)]

/-- A pointwise χ bound on the physical closed gap yields the action-gap estimate. -/
theorem sourceComplexAction_le_nine_of_gapFactor_bound (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n,
      ‖sourceCriticalRootRatioExtension hp hp1 n ψ z‖ ≤ K) :
    4*‖sourceComplexAction hp hp1 n ψ‖ ≤ 9*K*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := by
  have hnorm := (sourceRealGapFactor_norm_le_iff hp hp1 ψ hreal n K hK).mpr hbound
  exact (sourceComplexAction_le_nine_gapFactor_mul_gap_sq hp hp1 ψ hreal n).trans
    (by gcongr)

end NLS.ZakharovShabat
