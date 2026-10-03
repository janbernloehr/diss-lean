import NLS.ZakharovShabat.SourceCriticalRootRatioRealGapBound
import NLS.ZakharovShabat.SourceRealGapArcoshPrimitive
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Limits of partial horizontal gap integrals

Dominated convergence applies on every partial closed gap interval.
The endpoint weight is integrable, and the actual canonical side
quotients have the already proved signed arcosh integrals.
-/
noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A height approaches zero from the selected half-plane. -/
def sourceAbelianHeightSide (upper : Bool) : Set ℝ := if upper then Ioi 0 else Iio 0

theorem ne_zero_of_mem_sourceAbelianHeightSide (upper : Bool) {y : ℝ}
    (hy : y ∈ sourceAbelianHeightSide upper) : y ≠ 0 := by
  cases upper
  · exact (show y < 0 from hy).ne
  · exact (show 0 < y from hy).ne'

/-- Every partial actual quotient integral converges to its oriented
arcosh value as the horizontal path approaches the real gap. -/
theorem sourceAbelian_partialGapIntegral_tendsto
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    Tendsto (fun y : ℝ =>
      ∫ t in (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re..x,
        deriv (canonicalDiscriminant hp (periodOnePotential φ)) ((t : ℂ)+(y : ℂ)*I) /
          sourceCanonicalRoot hp hp1 φ ((t : ℂ)+(y : ℂ)*I))
      (𝓝[sourceAbelianHeightSide upper] 0)
      (𝓝 (if upper then (sourceRealGapArcoshProfile hp φ n x : ℂ)
        else -(sourceRealGapArcoshProfile hp φ n x : ℂ))) := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  by_cases he : a = x
  · have hleft := (sourceRealGapArcoshProfile_spec hp hp1 φ hφ n).2.1
    subst x
    simp only [a, intervalIntegral.integral_same, hleft, ofReal_zero, neg_zero, ite_self]
    exact tendsto_const_nhds
  have hax : a < x := lt_of_le_of_ne hx.1 he
  have hab : a < b := hax.trans_le hx.2
  let K : ℝ → ℂ := fun t => deriv (canonicalDiscriminant hp (periodOnePotential φ)) t /
    (if upper then realGapCanonicalRootUpperValue hp hp1 φ n t else
      sourceCanonicalRootGapLowerValue hp hp1 φ n (realGapInverseCoordinate hp hp1 φ n t))
  have hKI : (∫ t in a..x, K t) =
      (if upper then (sourceRealGapArcoshProfile hp φ n x : ℂ) else -(sourceRealGapArcoshProfile hp φ n x : ℂ)) := by
    cases upper
    · exact sourceRealGap_lowerIntegral_eq_neg_arcosh hp hp1 φ hφ n x hx
    · exact sourceRealGap_upperIntegral_eq_arcosh hp hp1 φ hφ n x hx
  rw [← hKI]
  obtain ⟨ε,M,hε,_,hbound⟩ := exists_sourceCriticalRootRatio_realGap_domination hp hp1 φ hφ n hab
  have hsmall : ∀ᶠ y in 𝓝[sourceAbelianHeightSide upper] (0 : ℝ), |y| < ε := by
    have hc : ContinuousAt (fun y : ℝ => |y|) 0 := continuous_abs.continuousAt
    exact (hc.tendsto.mono_left nhdsWithin_le_nhds).eventually (by simpa using! Iio_mem_nhds hε)
  have hweight : IntervalIntegrable (fun t : ℝ => M / Real.sqrt ((t-a)*(b-t))) volume a x := by
    have hw := (intervalIntegrable_inv_sqrt_endpoint_product hab).const_mul M
    apply (show IntervalIntegrable (fun t : ℝ => M / Real.sqrt ((t-a)*(b-t))) volume a b from
      by simpa only [div_eq_mul_inv] using hw).mono_set
    rw [Set.uIcc_of_le hx.1,Set.uIcc_of_le hab.le]
    exact Icc_subset_Icc le_rfl hx.2
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun t : ℝ => M / Real.sqrt ((t-a)*(b-t)))
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (continuous_sourceCriticalRootRatio_horizontal hp hp1 φ hφ y
      (ne_zero_of_mem_sourceAbelianHeightSide upper hy)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin,hsmall] with y hy hyε
    filter_upwards [ae_iff.mpr (show volume {t : ℝ | ¬t ≠ b} = 0 by simp)] with t htb ht
    have hti : t ∈ Ioc a x := by simpa only [uIoc_of_le hx.1] using ht
    exact hbound t ⟨hti.1,lt_of_le_of_ne (hti.2.trans hx.2) htb⟩ y
      (ne_zero_of_mem_sourceAbelianHeightSide upper hy) hyε.le
  · exact hweight
  · filter_upwards [ae_iff.mpr (show volume {t : ℝ | ¬t ≠ b} = 0 by simp)] with t htb ht
    have hti : t ∈ Ioc a x := by simpa only [uIoc_of_le hx.1] using ht
    have htgap : t ∈ Ioo a b := ⟨hti.1,lt_of_le_of_ne (hti.2.trans hx.2) htb⟩
    have hcoord := realGapInverseCoordinate_mem_Ioo hp hp1 φ n htgap
    cases upper
    · have h := sourceCriticalRootRatio_tendsto_vertical_lower hp hp1 φ hφ n hab
        (realGapInverseCoordinate hp hp1 φ n t) hcoord
      simpa only [sourceCanonicalRootGapPoint_inverseCoordinate hp hp1 φ hφ n hab t,K,
        sourceAbelianHeightSide,Bool.false_eq_true,ite_false] using! h
    · have h := sourceCriticalRootRatio_tendsto_vertical_upper hp hp1 φ hφ n hab
        (realGapInverseCoordinate hp hp1 φ n t) hcoord
      simpa only [sourceCanonicalRootGapPoint_inverseCoordinate hp hp1 φ hφ n hab t,K,
        sourceAbelianHeightSide,ite_true,realGapCanonicalRootUpperValue] using! h

end NLS.ZakharovShabat
