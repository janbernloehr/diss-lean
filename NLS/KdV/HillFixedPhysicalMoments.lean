import NLS.KdV.HillL2RealContourMoments
import NLS.KdV.HillLocalContourGeometry
import NLS.ComplexAnalysis.ConvexCutCirclePeriod
import NLS.ComplexAnalysis.RealCenteredCircleHomotopy

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Any real-centered isolating circle with the checked band and gap
geometry gives the original physical moment, including a collapsed gap. -/
theorem hillFixedContourMoment_eq_gapIntegral
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1≤n) (m : ℕ) (c R : ℝ) (hR : 0≤R)
    (hband : hillRealLabels q hq hr (2*n-2)<c-R ∧ c+R<hillRealLabels q hq hr (2*n+1))
    (hgap : segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ)⊆ball (c : ℂ) R) :
    -(Real.pi : ℂ)⁻¹*(∮ z in C((c : ℂ),R),z^m*hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z)=
      (hillRealGapIntegral q hq hr n m : ℂ) := by
  let Ω : Set ℂ := {z | z.re∈Ioo (hillRealLabels q hq hr (2*n-2)) (hillRealLabels q hq hr (2*n+1))}
  let K := segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ)
  have hΩ : IsOpen Ω := isOpen_Ioo.preimage continuous_re
  have hconv : Convex ℝ Ω := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  have hK : IsClosed K := by
    apply IsCompact.isClosed
    rw [show K=segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ) from rfl,
      segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hball0 : closedBall (c : ℂ) R⊆Ω := by
    intro z hz
    have hre := re_bounds_of_mem_realCenteredClosedBall hz
    exact ⟨by linarith [hband.1,hre.1],by linarith [hband.2,hre.2]⟩
  have hball1 : closedBall (hillRealGapCenter q hq hr n : ℂ)
      (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n)⊆Ω :=
    fun z hz => hillRealGapContour_closedBall_real_bounds q hq hr n hn z hz
  have hf : DifferentiableOn ℂ (fun z => z^m*hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z) (Ω \ K) := by
    intro z hz
    have hcut := mem_hillL2RealCutDomain_of_filled_not_gap q hq hr n hn z (Or.inr hz.1) hz.2
    exact ((analyticAt_id.pow m).mul (analyticOnNhd_hillL2RealCutPrimitive q hq hr z hcut)).differentiableAt.differentiableWithinAt
  have he := circleIntegral_eq_of_convex_cut_domain
    (fun z => z^m*hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z) Ω K
    (c : ℂ) (hillRealGapCenter q hq hr n : ℂ) R
    (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n)
    hΩ hconv hK hR
    (add_nonneg (hillRealGapContour_geometry q hq hr n hn).1 (hillRealGapContour_geometry q hq hr n hn).2.1.le)
    hball0 hball1 hgap (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr n hn) hf
  rw [he]
  exact hillL2RealContourMoment_eq_gapIntegral q hq hr n hn m

end NLS.KdV
