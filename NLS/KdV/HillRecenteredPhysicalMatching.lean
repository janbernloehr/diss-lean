import NLS.KdV.HillRecenteredTracePrimitives
import NLS.KdV.HillRealPeriodOneAffinePath
import NLS.ComplexAnalysis.ContinuousTracePrimitiveUniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



theorem mem_hillRecenteredContinuationDomain_nonreal
    (q r : RealPeriodOneHillPotential) (z : ℂ) (him : z.im≠0) :
    (z,SpectralWeight.one.toCoeff r.val-SpectralWeight.one.toCoeff q.val)∈
      hillRecenteredContinuationDomain q.val q.property.1 q.property.2 := by
  apply (mem_hillRecenteredContinuationDomain_iff q.val q.property.1 q.property.2 _).mpr
  refine ⟨Or.inl him,?_⟩
  intro s _
  have hh := hillL2Radicand_ne_zero_on_realCutDomain
    (hillRealPeriodOneAffinePath q r s).val (hillRealPeriodOneAffinePath q r s).property.1
    (hillRealPeriodOneAffinePath q r s).property.2 z (Or.inl him)
  simpa only [hillRealPeriodOneAffinePath_coeff] using hh

/-- The actual recentered logarithm agrees with the physical rough
primitive at every real source and nonreal energy, by branch uniqueness
along the real affine path. -/
theorem hillRecenteredPrimitive_eq_physical_nonreal
    (q r : RealPeriodOneHillPotential) (z : ℂ) (him : z.im≠0) :
    hillRecenteredPrimitive q.val q.property.1 q.property.2
      (z,SpectralWeight.one.toCoeff r.val-SpectralWeight.one.toCoeff q.val)=
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff r.val) z := by
  let D := SpectralWeight.one.toCoeff r.val-SpectralWeight.one.toCoeff q.val
  let F (t : ℝ) := hillRecenteredPrimitive q.val q.property.1 q.property.2 (z,(t : ℂ) • D)
  let G (t : ℝ) := hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff (hillRealPeriodOneAffinePath q r t).val)
  have hend : (z,D)∈hillRecenteredContinuationDomain q.val q.property.1 q.property.2 :=
    mem_hillRecenteredContinuationDomain_nonreal q r z him
  have hnew (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
      (z,(t : ℂ) • D)∈hillRecenteredContinuationDomain q.val q.property.1 q.property.2 := by
    have hh := (hillRecenteredTraceFamily q.val q.property.1 q.property.2).continuationDomain_segment (z,D) hend t ht
    simpa only [hillRecenteredContinuationDomain,sourceSegmentMap,zero_add,sub_zero] using hh
  have hold (t : ℝ) :
      (z,SpectralWeight.one.toCoeff (hillRealPeriodOneAffinePath q r t).val)∈hillL2ContinuationDomain :=
    mem_hillL2ContinuationDomain_of_im_ne_zero (hillRealPeriodOneAffinePath q r t).val
      (hillRealPeriodOneAffinePath q r t).property.1 (hillRealPeriodOneAffinePath q r t).property.2 z him
  have hF : ContinuousOn F (Icc (0 : ℝ) 1) :=
    (analyticOnNhd_hillRecenteredPrimitive q.val q.property.1 q.property.2).continuousOn.comp
      (continuous_const.prodMk (continuous_ofReal.smul continuous_const)).continuousOn hnew
  have hpath : Continuous (fun t : ℝ => (z,SpectralWeight.one.toCoeff (hillRealPeriodOneAffinePath q r t).val)) :=
    continuous_const.prodMk ((SpectralWeight.one.toCoeff).continuous.comp
      (continuous_subtype_val.comp (continuous_hillRealPeriodOneAffinePath q r)))
  have hG : ContinuousOn G (Icc (0 : ℝ) 1) :=
    analyticOnNhd_hillL2ContinuedPrimitive.continuousOn.comp hpath.continuousOn (fun t _ => hold t)
  have htrace (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : 2*cosh (F t)=2*cosh (G t) := by
    dsimp only [F,G]
    rw [(hillRecenteredPrimitive_trace q.val q.property.1 q.property.2 (z,(t : ℂ) • D) (hnew t ht)).1,
      (hillL2ContinuedPrimitive_trace _ (hold t)).1,hillRealPeriodOneAffinePath_coeff]
  have hne (t : ℝ) (_ : t∈Icc (0 : ℝ) 1) : 2*sinh (G t)≠0 := by
    dsimp only [G]
    rw [(hillL2ContinuedPrimitive_trace _ (hold t)).2]
    exact hillL2ContinuedRoot_ne_zero _ (hold t)
  have hbase : F 0=G 0 := by
    simp only [F,G,ofReal_zero,zero_smul,hillRecenteredPrimitive_base,hillRealPeriodOneAffinePath_zero,
      hillL2RealCutPrimitive,if_neg him]
  have he := continuousCoshPrimitives_eqOn F G (Icc (0 : ℝ) 1) isPreconnected_Icc hF hG htrace hne
    0 (by norm_num) hbase (by norm_num : (1 : ℝ)∈Icc 0 1)
  simpa only [F,G,ofReal_one,one_smul,hillRealPeriodOneAffinePath_one,hillL2RealCutPrimitive,if_neg him] using he

theorem hillRecenteredRoot_eq_physical_nonreal
    (q r : RealPeriodOneHillPotential) (z : ℂ) (him : z.im≠0) :
    hillRecenteredRoot q.val q.property.1 q.property.2
      (z,SpectralWeight.one.toCoeff r.val-SpectralWeight.one.toCoeff q.val)=
      hillL2RealCutRoot (SpectralWeight.one.toCoeff r.val) z := by
  rw [← (hillRecenteredPrimitive_trace q.val q.property.1 q.property.2 _
    (mem_hillRecenteredContinuationDomain_nonreal q r z him)).2,
    hillRecenteredPrimitive_eq_physical_nonreal q r z him]
  rfl

end NLS.KdV
