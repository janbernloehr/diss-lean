import NLS.KdV.HillL2RealContourMoments
import NLS.KdV.HillAbelianComplexRoot
import NLS.ComplexAnalysis.TracePrimitiveMomentDifferential

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem tracePrimitive_mem_base
    {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
    (f : TracePrimitiveFamily A) (z : ℂ) (hz : z∈f.freeDomain)
    (hne : f.radicand (z,0)≠0) : (z,0)∈f.continuationDomain := by
  intro s _
  simpa only [sourceSegmentMap,zero_add,sub_zero,smul_zero] using
    (show (z,0)∈f.rootDomain from ⟨hz,hne⟩)

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual Hill trace family based at an arbitrary real source.
Its reference logarithm is the original physical cut primitive. -/
def hillRecenteredTraceFamily : TracePrimitiveFamily (Coeff 2) where
  trace := fun t => hillL2Discriminant (t.2+SpectralWeight.one.toCoeff q) t.1
  analytic_trace := by
    intro t _
    exact (analyticOnNhd_hillL2Discriminant_joint (t.1,t.2+SpectralWeight.one.toCoeff q) (mem_univ _)).comp
      (f := fun p : ℂ × Coeff 2 => (p.1,p.2+SpectralWeight.one.toCoeff q))
      (analyticAt_fst.prod (analyticAt_snd.add analyticAt_const))
  freePrimitive := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)
  freeDomain := hillL2RealCutDomain q hq hr
  isOpen_freeDomain := isOpen_hillL2RealCutDomain q hq hr
  analytic_freePrimitive := analyticOnNhd_hillL2RealCutPrimitive q hq hr
  free_trace := fun z => by simpa only [zero_add] using hillL2RealCutPrimitive_trace q hq hr z

def hillRecenteredContinuationDomain : Set (ℂ × Coeff 2) :=
  (hillRecenteredTraceFamily q hq hr).continuationDomain

def hillRecenteredRoot : ℂ × Coeff 2 → ℂ := (hillRecenteredTraceFamily q hq hr).root

def hillRecenteredPrimitive : ℂ × Coeff 2 → ℂ := (hillRecenteredTraceFamily q hq hr).primitive

theorem isOpen_hillRecenteredContinuationDomain : IsOpen (hillRecenteredContinuationDomain q hq hr) :=
  (hillRecenteredTraceFamily q hq hr).isOpen_continuationDomain

theorem analyticOnNhd_hillRecenteredRoot :
    AnalyticOnNhd ℂ (hillRecenteredRoot q hq hr) (hillRecenteredContinuationDomain q hq hr) :=
  (hillRecenteredTraceFamily q hq hr).analytic_root

theorem analyticOnNhd_hillRecenteredPrimitive :
    AnalyticOnNhd ℂ (hillRecenteredPrimitive q hq hr) (hillRecenteredContinuationDomain q hq hr) :=
  (hillRecenteredTraceFamily q hq hr).analytic_primitive

theorem hillRecenteredPrimitive_base (z : ℂ) :
    hillRecenteredPrimitive q hq hr (z,0)=hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z :=
  (hillRecenteredTraceFamily q hq hr).primitive_base z

theorem hillRecenteredRoot_base (z : ℂ) :
    hillRecenteredRoot q hq hr (z,0)=hillL2RealCutRoot (SpectralWeight.one.toCoeff q) z :=
  (hillRecenteredTraceFamily q hq hr).root_base z

theorem hillRecenteredRoot_sq (t : ℂ × Coeff 2) (ht : t∈hillRecenteredContinuationDomain q hq hr) :
    (hillRecenteredRoot q hq hr t)^2=hillL2Radicand (t.2+SpectralWeight.one.toCoeff q) t.1 :=
  (hillRecenteredTraceFamily q hq hr).root_sq t ht

theorem hillRecenteredPrimitive_trace (t : ℂ × Coeff 2) (ht : t∈hillRecenteredContinuationDomain q hq hr) :
    2*cosh (hillRecenteredPrimitive q hq hr t)=hillL2Discriminant (t.2+SpectralWeight.one.toCoeff q) t.1 ∧
      2*sinh (hillRecenteredPrimitive q hq hr t)=hillRecenteredRoot q hq hr t :=
  (hillRecenteredTraceFamily q hq hr).primitive_trace t ht

theorem mem_hillRecenteredContinuationDomain_iff (t : ℂ × Coeff 2) :
    t∈hillRecenteredContinuationDomain q hq hr ↔ t.1∈hillL2RealCutDomain q hq hr ∧
      ∀ s∈Icc (0 : ℝ) 1, hillL2Radicand ((s : ℂ) • t.2+SpectralWeight.one.toCoeff q) t.1≠0 := by
  constructor
  · intro ht
    refine ⟨((hillRecenteredTraceFamily q hq hr).continuationDomain_subset ht).1,?_⟩
    intro s hs
    simpa only [TracePrimitiveFamily.radicand,hillL2Radicand,hillRecenteredTraceFamily,sourceSegmentMap,zero_add,sub_zero] using (ht s hs).2
  · rintro ⟨hfree,hne⟩ s hs
    refine ⟨hfree,?_⟩
    simpa only [TracePrimitiveFamily.radicand,hillL2Radicand,hillRecenteredTraceFamily,sourceSegmentMap,zero_add,sub_zero] using hne s hs

theorem mem_hillRecenteredContinuationDomain_base (z : ℂ) (hz : z∈hillL2RealCutDomain q hq hr) :
    (z,0)∈hillRecenteredContinuationDomain q hq hr := by
  apply tracePrimitive_mem_base (hillRecenteredTraceFamily q hq hr) z hz
  change hillL2Radicand ((0 : Coeff 2)+SpectralWeight.one.toCoeff q) z≠0
  rw [zero_add]
  exact hillL2Radicand_ne_zero_on_realCutDomain q hq hr z hz

/-- A compact physical contour has one genuine complex source
neighborhood for the recentered logarithm, with no high-energy cutoff. -/
theorem exists_hillRecenteredPrimitive_contour_neighborhood (c : ℂ) (r : ℝ)
    (hc : sphere c r⊆hillL2RealCutDomain q hq hr) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ (0 : Coeff 2)∈V ∧
      sphere c r ×ˢ V⊆hillRecenteredContinuationDomain q hq hr :=
  (hillRecenteredTraceFamily q hq hr).exists_continuation_neighborhood (sphere c r) (isCompact_sphere c r)
    0 (fun z hz => mem_hillRecenteredContinuationDomain_base q hq hr z (hc hz))

end NLS.KdV
