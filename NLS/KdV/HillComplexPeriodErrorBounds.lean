import NLS.KdV.HillComplexPeriodIntegrandBounds
import NLS.ComplexAnalysis.NormalizedCircleIntegralBounds
import NLS.KdV.HillCommonComplexPeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillAbelianHilbertIntegrand_circleIntegrable (n k : ℕ) (hk : 1 ≤ k) (a : Coeff 2) :
    CircleIntegrable (fun E => hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 hq hr E)
      (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k) := by
  apply ContinuousOn.circleIntegrable
    (add_nonneg (hillRealGapContour_geometry 0 hq hr k hk).1 (hillRealGapContour_geometry 0 hq hr k hk).2.1.le)
  intro E hE
  have hcut := hillRealGapContour_sphere_subset 0 hq hr k hk hE
  have hN : AnalyticAt ℂ (fun z : ℂ => hillAbelianHilbertPsi n (z,a)) E :=
    (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  exact (hN.div (analyticOnNhd_hillEnergyCanonicalRootProduct 0 hq hr E hcut)
    (hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 hq hr E hcut)).continuousAt.continuousWithinAt

theorem norm_scaled_hillAbelianComplexPeriod_error_le (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hnk : n ≠ k) (a p : Coeff 2) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
      (E,p) ∈ hillAbelianComplexRootDomain 0 hq hr)
    (hbound : ∀ E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
      ‖hillEnergyCanonicalRootProduct 0 hq hr E/hillAbelianComplexRoot 0 hq hr (E,p)-1‖ ≤
        C*‖p‖/(k : ℝ)) :
    ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
      2*Real.pi^2*C*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ) := by
  let R := hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k
  have hR : 0 ≤ R := add_nonneg (hillRealGapContour_geometry 0 hq hr k hk).1
    (hillRealGapContour_geometry 0 hq hr k hk).2.1.le
  have hRle : R ≤ (k : ℝ)*Real.pi^2/2 := by
    dsimp only [R]
    rw [hillFreeGapHalfLength hq hr k hk,zero_add,hillFreeGapCollar hq hr k hk]
    nlinarith only [sq_nonneg Real.pi]
  have h := norm_normalized_circleIntegral_difference_le
    (fun E => hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 hq hr (E,p))
    (fun E => hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 hq hr E)
    (hillRealGapCenter 0 hq hr k : ℂ)
    (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ)) R
    (4*C*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ)^2) hR
    (hillAbelianComplexIntegrand_circleIntegrable hq hr n k hk a p hdom)
    (hillAbelianHilbertIntegrand_circleIntegrable hq hr n k hk a)
    (fun E hE => norm_scaled_hillAbelianComplexIntegrand_error_le hq hr n k hn hk hnk E hE a p C
      (hdom E hE) (hbound E hE))
  change ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤ _ at h
  apply h.trans
  apply (mul_le_mul_of_nonneg_right hRle (by positivity)).trans_eq
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp
  ring

end NLS.KdV
