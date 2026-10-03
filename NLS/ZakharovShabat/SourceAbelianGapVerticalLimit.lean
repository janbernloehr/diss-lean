import NLS.ZakharovShabat.SourceAbelianPartialGapLimit
import NLS.ZakharovShabat.SourceAbelianPrimitiveProperties

/-! # The exact vertical gap-side limits of the abelian primitive

At nonzero height the fundamental theorem evaluates each partial
horizontal integral as a difference of half-plane primitive values.
The normalized endpoint tends to zero, so dominated convergence gives
the signed arcosh boundary value with no logarithm-period ambiguity.
-/
noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAbelian_vertical_mem_halfPlane (upper : Bool) (x y : ℝ)
    (hy : y ∈ sourceAbelianHeightSide upper) : (x : ℂ)+(y : ℂ)*I ∈ sourceAbelianHalfPlane upper := by
  cases upper <;> simpa only [sourceAbelianHalfPlane,sourceAbelianHeightSide,Bool.false_eq_true,ite_true,ite_false,mem_Ioi,mem_Iio,
    mem_ofPred_eq,add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,zero_add,add_zero] using! hy

/-- The nonzero-height partial integral equals the actual normalized
half-plane primitive difference. The real endpoints may be arbitrary. -/
theorem sourceAbelianHalfPlanePrimitive_horizontal_integral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) (a x y : ℝ)
    (hy : y ∈ sourceAbelianHeightSide upper) :
    (∫ t in a..x, deriv (canonicalDiscriminant hp (periodOnePotential φ)) ((t : ℂ)+(y : ℂ)*I) /
      sourceCanonicalRoot hp hp1 φ ((t : ℂ)+(y : ℂ)*I)) =
    sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper ((x : ℂ)+(y : ℂ)*I) -
      sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper ((a : ℂ)+(y : ℂ)*I) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    have hF := (sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ n upper).1 _
      (sourceAbelian_vertical_mem_halfPlane upper t y hy)
    have hmap : HasDerivAt (fun r : ℝ => (r : ℂ)+(y : ℂ)*I) 1 t := by
      simpa only [id_eq] using! ((hasDerivAt_id (t : ℂ)).comp_ofReal).add_const ((y : ℂ)*I)
    simpa only [Function.comp_def,smul_eq_mul,one_mul] using! hF.scomp t hmap
  · exact (continuous_sourceCriticalRootRatio_horizontal hp hp1 φ hφ y
      (ne_zero_of_mem_sourceAbelianHeightSide upper hy)).intervalIntegrable a x

/-- Lemma 19.1(v) along the upper and lower vertical approaches, for
every point of the closed gap and every signed index. -/
theorem sourceAbelianHalfPlanePrimitive_gap_vertical_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    Tendsto (fun y : ℝ => sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper ((x : ℂ)+(y : ℂ)*I))
      (𝓝[sourceAbelianHeightSide upper] 0)
      (𝓝 (if upper then (sourceRealGapArcoshProfile hp φ n x : ℂ)
        else -(sourceRealGapArcoshProfile hp φ n x : ℂ))) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  have hl : l.im = 0 := (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).1
  have hlreal : (l.re : ℂ) = l := Complex.ext rfl hl.symm
  have hmap : Tendsto (fun y : ℝ => (l.re : ℂ)+(y : ℂ)*I)
      (𝓝[sourceAbelianHeightSide upper] 0) (𝓝[sourceAbelianHalfPlane upper] l) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun y : ℝ => (l.re : ℂ)+(y : ℂ)*I) := by fun_prop
      simpa only [ofReal_zero,zero_mul,add_zero,hlreal] using
        (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact sourceAbelian_vertical_mem_halfPlane upper l.re y hy
  have hleft := (sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ n upper).2.1.comp hmap
  have hlim := (sourceAbelian_partialGapIntegral_tendsto hp hp1 φ hφ n upper x hx).add hleft
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have he := sourceAbelianHalfPlanePrimitive_horizontal_integral hp hp1 φ hφ n upper l.re x y hy
  rw [he]
  exact sub_add_cancel _ _

/-- The same signed boundary formula for the global primitive, with
the index normalization added explicitly. -/
theorem sourceAbelianPrimitive_gap_vertical_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    Tendsto (fun y : ℝ => sourceAbelianPrimitive hp hp1 φ hφ ((x : ℂ)+(y : ℂ)*I)+I*(Real.pi : ℂ)*n)
      (𝓝[sourceAbelianHeightSide upper] 0)
      (𝓝 (if upper then (sourceRealGapArcoshProfile hp φ n x : ℂ)
        else -(sourceRealGapArcoshProfile hp φ n x : ℂ))) := by
  apply (sourceAbelianHalfPlanePrimitive_gap_vertical_limit hp hp1 φ hφ n upper x hx).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hz := sourceAbelian_vertical_mem_halfPlane upper x y hy
  rw [sourceAbelianPrimitive_eq_global hp hp1 φ hφ
      (sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ upper hz),
    sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 φ hφ upper hz]
  exact sourceAbelianHalfPlanePrimitive_eq_zeroIndex_add hp hp1 φ hφ n upper hz

end NLS.ZakharovShabat
