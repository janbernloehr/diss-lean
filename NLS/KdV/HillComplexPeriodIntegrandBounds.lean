import NLS.KdV.HillContourHilbertPsiBounds
import NLS.KdV.HillComplexContourInverseRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem norm_scaled_hillAbelianComplexIntegrand_error_le (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hnk : n ≠ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k))
    (a p : Coeff 2) (C : ℝ) (hdom : (E,p) ∈ hillAbelianComplexRootDomain 0 hq hr)
    (hbound : ‖hillEnergyCanonicalRootProduct 0 hq hr E/hillAbelianComplexRoot 0 hq hr (E,p)-1‖ ≤
      C*‖p‖/(k : ℝ)) :
    ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 hq hr (E,p)-
        hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 hq hr E)‖ ≤
      4*C*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ)^2 := by
  have hR := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 hq hr E hdom.1.1
  have hP := hillAbelianComplexRoot_ne_zero 0 hq hr (E,p) hdom
  have he : (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 hq hr (E,p)-
        hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 hq hr E) =
      ((((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 hq hr E))*
      (hillEnergyCanonicalRootProduct 0 hq hr E/hillAbelianComplexRoot 0 hq hr (E,p)-1) := by
    field_simp
  rw [he,norm_mul]
  apply (mul_le_mul (norm_scaled_hillAbelianHilbertPsi_free_root_le hq hr n k hn hk hnk E hE a)
    hbound (norm_nonneg _) (by positivity)).trans_eq
  ring

theorem hillAbelianComplexIntegrand_circleIntegrable (n k : ℕ) (hk : 1 ≤ k) (a p : Coeff 2)
    (hdom : ∀ E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
      (E,p) ∈ hillAbelianComplexRootDomain 0 hq hr) :
    CircleIntegrable (fun E => hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 hq hr (E,p))
      (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k) := by
  apply ContinuousOn.circleIntegrable
    (add_nonneg (hillRealGapContour_geometry 0 hq hr k hk).1 (hillRealGapContour_geometry 0 hq hr k hk).2.1.le)
  intro E hE
  have hN : AnalyticAt ℂ (fun z : ℂ => hillAbelianHilbertPsi n (z,a)) E :=
    (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  have hD : AnalyticAt ℂ (fun z : ℂ => hillAbelianComplexRoot 0 hq hr (z,p)) E :=
    (analyticOnNhd_hillAbelianComplexRoot 0 hq hr (E,p) (hdom E hE)).comp
      (f := fun z : ℂ => (z,p)) (analyticAt_id.prod analyticAt_const)
  exact (hN.div hD (hillAbelianComplexRoot_ne_zero 0 hq hr (E,p) (hdom E hE))).continuousAt.continuousWithinAt

end NLS.KdV
