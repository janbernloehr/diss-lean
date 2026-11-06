import NLS.KdV.HillRecenteredPhysicalMatching
import NLS.KdV.HillFixedPhysicalMoments
import NLS.ComplexAnalysis.NonrealCircleIntegralComparison

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- A fixed intrinsic-circle moment based at the original real source,
expressed in the full complex coefficient variable rather than its offset. -/
def hillRealSourceMoment (n m : ℕ) (p : Coeff 2) : ℂ :=
  (hillRecenteredTraceFamily q hq hr).contourMoment (hillRealGapCenter q hq hr n : ℂ)
    (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n) m (p-SpectralWeight.one.toCoeff q)

theorem analyticAt_hillRealSourceMoment (n : ℕ) (hn : 1≤n) (m : ℕ) :
    AnalyticAt ℂ (hillRealSourceMoment q hq hr n m) (SpectralWeight.one.toCoeff q) := by
  have hRad : 0≤hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n :=
    add_nonneg (hillRealGapContour_geometry q hq hr n hn).1 (hillRealGapContour_geometry q hq hr n hn).2.1.le
  obtain ⟨V,_,h0V,hA⟩ := (hillRecenteredTraceFamily q hq hr).exists_analytic_contourMoment
    (hillRealGapCenter q hq hr n : ℂ) (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n)
    hRad 0 (fun z hz => mem_hillRecenteredContinuationDomain_base q hq hr z
      (hillRealGapContour_sphere_subset q hq hr n hn hz)) m
  have hbase : AnalyticAt ℂ ((hillRecenteredTraceFamily q hq hr).contourMoment
      (hillRealGapCenter q hq hr n : ℂ) (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n) m)
      (SpectralWeight.one.toCoeff q-SpectralWeight.one.toCoeff q) := by
    simpa only [sub_self] using hA 0 h0V
  exact hbase.comp (f := fun p : Coeff 2 => p-SpectralWeight.one.toCoeff q) (analyticAt_id.sub analyticAt_const)

/-- The recentered moment germs match every original physical moment
on one real neighborhood per gap, chosen before the hierarchy order.
No gap-openness or high-energy hypothesis is used. -/
theorem exists_hillRealSourceMoments_physical_neighborhood (n : ℕ) (hn : 1≤n) :
    ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      ∀ r∈V, ∀ m : ℕ, hillRealSourceMoment q hq hr n m (SpectralWeight.one.toCoeff r.val)=
        (hillRealGapIntegral r.val r.property.1 r.property.2 n m : ℂ) := by
  obtain ⟨V,hV,hqV,hgeo⟩ := exists_hillIntrinsicContour_local_physical_geometry q hq hr n hn
  refine ⟨V,hV,hqV,?_⟩
  intro r hrV m
  let c := hillRealGapCenter q hq hr n
  let R := hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr n hn).1
    (hillRealGapContour_geometry q hq hr n hn).2.1
  have he : (∮ z in C((c : ℂ),R),z^m*hillRecenteredPrimitive q hq hr
      (z,SpectralWeight.one.toCoeff r.val-SpectralWeight.one.toCoeff q))=
      ∮ z in C((c : ℂ),R),z^m*hillL2RealCutPrimitive (SpectralWeight.one.toCoeff r.val) z := by
    apply circleIntegral_eq_of_eq_on_nonreal _ _ c R hR
    intro z _ him
    rw [hillRecenteredPrimitive_eq_physical_nonreal (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) r z him]
  change -(Real.pi : ℂ)⁻¹*(∮ z in C((c : ℂ),R),z^m*hillRecenteredPrimitive q hq hr
    (z,SpectralWeight.one.toCoeff r.val-SpectralWeight.one.toCoeff q))=_
  rw [he]
  exact hillFixedContourMoment_eq_gapIntegral r.val r.property.1 r.property.2 n hn m c R hR.le
    (hgeo r hrV).1 (hgeo r hrV).2

end NLS.KdV
