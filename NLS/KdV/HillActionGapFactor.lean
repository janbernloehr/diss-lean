import NLS.KdV.HillDeflatedTraceCharts
import NLS.KdV.HillEnergyRootIdentification
import NLS.KdV.HillRealGapContourDiscs
import NLS.ComplexAnalysis.QuadraticGapActionMoment
import NLS.ComplexAnalysis.RealCenteredCircleHomotopy

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillActionGapRatio (n : ℕ) : ℂ :=
  (-2*I/(Real.pi : ℂ))*(∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*
    deriv (hillDeflatedTraceNumerator q hq hr n)
      ((hillRealGapCenter q hq hr n : ℂ)+(hillRealGapHalfLength q hq hr n : ℂ)*(Real.cos θ : ℂ)))

theorem hillRealGapIntegral_eq_halfLength_sq_mul_ratio (n : ℕ) (hn : 1 ≤ n) :
    (hillRealGapIntegral q hq hr n 0 : ℂ) =
      (hillRealGapHalfLength q hq hr n : ℂ)^2*hillActionGapRatio q hq hr n := by
  let τ := hillRealGapCenter q hq hr n
  let δ := hillRealGapHalfLength q hq hr n
  let r := δ+hillRealGapCollar q hq hr n
  let l := hillRealLabels q hq hr (2*n-2)
  let u := hillRealLabels q hq hr (2*n+1)
  obtain ⟨hd,hη,hl,hu,_⟩ := hillRealGapContour_geometry q hq hr n hn
  have hRad : 0 < r := add_pos_of_nonneg_of_pos hd hη
  have hb := hillRealGapContour_band_bounds q hq hr n hn
  let b := min (τ-l) (u-τ)
  have hrb : r < b := lt_min (by linarith [hb.1]) (by linarith [hb.2])
  let R := (r+b)/2
  have hrR : r < R := by dsimp [R];linarith
  have hRb : R < b := by dsimp [R];linarith
  have hleft : l < τ-R := by have h := min_le_left (τ-l) (u-τ);change R < min (τ-l) (u-τ) at hRb;linarith
  have hright : τ+R < u := by have h := min_le_right (τ-l) (u-τ);change R < min (τ-l) (u-τ) at hRb;linarith
  have hfill : closedBall (τ : ℂ) R ⊆ hillGapFilledDomain q hq hr n := by
    intro z hz
    have hre := re_bounds_of_mem_realCenteredClosedBall hz
    exact Or.inr ⟨by linarith [hre.1],by linarith [hre.2]⟩
  have hH := (analyticOnNhd_hillDeflatedTraceNumerator q hq hr n hn).mono hfill
  have hδr : ‖(δ : ℂ)‖ < r := by rw [norm_real,Real.norm_eq_abs,abs_of_nonneg hd];dsimp [r,δ];linarith
  have hL : (τ : ℂ)-(δ : ℂ) = (hillRealLabels q hq hr (2*n-1) : ℂ) := by rw [← ofReal_sub,hl]
  have hU : (τ : ℂ)+(δ : ℂ) = (hillRealLabels q hq hr (2*n) : ℂ) := by rw [← ofReal_add,hu]
  have he (z : ℂ) : hillDeflatedTraceNumerator q hq hr n z/endpointRoot ((τ : ℂ)-δ) ((τ : ℂ)+δ) z =
      deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z/hillEnergyCanonicalRootProduct q hq hr z := by
    rw [hL,hU,hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated q hq hr n hn z,hillDeflatedTraceNumerator,div_div]
    congr 1
    ring
  have hz : (∮ z in C((τ : ℂ),r), hillDeflatedTraceNumerator q hq hr n z/endpointRoot ((τ : ℂ)-δ) ((τ : ℂ)+δ) z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hRad.le
    intro z hz
    rw [he z]
    exact (hasDerivAt_hillL2RealCutPrimitive_energyProduct q hq hr z (hillRealGapContour_sphere_subset q hq hr n hn hz)).hasDerivWithinAt
  have hmoment := circleIntegral_mul_div_endpointRoot_eq_squared_gap (hillDeflatedTraceNumerator q hq hr n)
    (τ : ℂ) (δ : ℂ) r R hδr hrR hH hz
  have hsource := (hillL2RealContourMoment_eq_gapIntegral q hq hr n hn 0).symm.trans
    (hillL2RealContourMoment_arnold_energyProduct q hq hr n hn 0)
  simp only [Nat.cast_zero,zero_add,one_mul,pow_one] at hsource
  have hcontour : (∮ z in C((τ : ℂ),r), z*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
      hillEnergyCanonicalRootProduct q hq hr z) =
      ∮ z in C((τ : ℂ),r), z*hillDeflatedTraceNumerator q hq hr n z/endpointRoot ((τ : ℂ)-δ) ((τ : ℂ)+δ) z := by
    apply circleIntegral.integral_congr hRad.le
    intro z _
    simp only [mul_div_assoc,he z]
  rw [hcontour,hmoment] at hsource
  exact hsource.trans (by dsimp [hillActionGapRatio,τ,δ];ring)

end NLS.KdV
