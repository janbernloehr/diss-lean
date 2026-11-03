import NLS.KdV.HillGlobalDifferentialReality
import NLS.KdV.HillDeflatedCanonicalRootPhase
import NLS.KdV.HillFilledGapCutDomain
import NLS.ComplexAnalysis.CosineSegmentGeometry

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillAbelianCosineDifferential (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (θ : ℂ) : ℂ :=
  -I * (hillAbelianSelectedGlobalPsi q hq hr n hn
    (cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) θ)/
    hillDeflatedEnergyCanonicalRoot q hq hr k
      (cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) θ))

theorem hillCosineGapPoint_mem_real_gap (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) :
    cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (θ : ℂ) ∈
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) := by
  have hgeom := hillRealGapContour_geometry q hq hr k hk
  have hl : (hillRealGapCenter q hq hr k : ℂ)-(hillRealGapHalfLength q hq hr k : ℂ) =
      (hillRealLabels q hq hr (2*k-1) : ℂ) := by rw [← ofReal_sub,hgeom.2.2.1]
  have hu : (hillRealGapCenter q hq hr k : ℂ)+(hillRealGapHalfLength q hq hr k : ℂ) =
      (hillRealLabels q hq hr (2*k) : ℂ) := by rw [← ofReal_add,hgeom.2.2.2.1]
  simpa only [hl,hu] using cosineGapPoint_real_mem_segment
    (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k : ℂ) θ

theorem hillCosineGapPoint_mem_filledDomain (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) :
    cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (θ : ℂ) ∈
      hillGapFilledDomain q hq hr k := by
  have he := hillCosineGapPoint_mem_real_gap q hq hr k hk θ
  have hball := hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk he
  exact hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk (ball_subset_closedBall hball)

theorem analyticAt_hillAbelianCosineDifferential_real (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) :
    AnalyticAt ℂ (hillAbelianCosineDifferential q hq hr n hn k) (θ : ℂ) := by
  let E := cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (θ : ℂ)
  have hE : E ∈ hillGapFilledDomain q hq hr k := hillCosineGapPoint_mem_filledDomain q hq hr k hk θ
  have hJ : AnalyticAt ℂ (cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k)) (θ : ℂ) := by
    unfold cosineGapPoint
    exact analyticAt_const.add (analyticAt_const.mul Complex.analyticAt_cos)
  have hN := (analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn E (mem_univ _)).comp
    (f := cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k)) hJ
  have hD := (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k E hE).comp
    (f := cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k)) hJ
  exact analyticAt_const.mul (hN.div hD (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk E hE))

theorem hillAbelianCosineDifferential_im_eq_zero (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) :
    (hillAbelianCosineDifferential q hq hr n hn k (θ : ℂ)).im = 0 := by
  let E := cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (θ : ℂ)
  have hseg := hillCosineGapPoint_mem_real_gap q hq hr k hk θ
  have hEim : E.im = 0 := im_eq_zero_of_mem_real_segment _ _ E hseg
  have he : E = (E.re : ℂ) := by apply Complex.ext <;> simp [hEim]
  have hx := re_mem_Icc_of_mem_real_segment _ _ (monotone_hillRealLabels q hq hr (by omega : 2*k-1 ≤ 2*k)) E hseg
  have hN : (hillAbelianSelectedGlobalPsi q hq hr n hn (E.re : ℂ)).im = 0 := by
    have hc := hillAbelianSelectedGlobalPsi_conj q hq hr n hn (E.re : ℂ)
    rw [conj_ofReal] at hc
    exact Complex.conj_eq_iff_im.mp hc.symm
  have hrot := im_I_mul_div_hillDeflatedEnergyCanonicalRoot_eq_zero_on_gap q hq hr k hk E.re hx _ hN
  change (-I*(hillAbelianSelectedGlobalPsi q hq hr n hn E/hillDeflatedEnergyCanonicalRoot q hq hr k E)).im = 0
  rw [he,neg_mul,neg_im,hrot,neg_zero]

end NLS.KdV
