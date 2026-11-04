import NLS.KdV.HillRootSlopeNonvanishing
import NLS.KdV.HillIntrinsicPeriodReality

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillIntrinsicGapPeriod_circleIntegrable (k : ℕ) (hk : 1 ≤ k) (N : ℂ → ℂ)
    (hN : AnalyticOnNhd ℂ N univ) :
    CircleIntegrable (fun E => N E/hillEnergyCanonicalRootProduct q hq hr E)
      (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) := by
  have hs := hillRealGapContour_sphere_subset q hq hr k hk
  have hc : ContinuousOn (fun E => N E/hillEnergyCanonicalRootProduct q hq hr E)
      (sphere (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :=
    (hN.continuousOn.mono (subset_univ _)).div
      ((analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr).continuousOn.mono hs)
      (fun E hE => hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr E (hs hE))
  exact hc.circleIntegrable (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1.le)

theorem hillIntrinsicGapPeriod_const_mul (k : ℕ) (N : ℂ → ℂ) (c : ℂ) :
    hillIntrinsicGapPeriod q hq hr k (fun E => c*N E) = c*hillIntrinsicGapPeriod q hq hr k N := by
  unfold hillIntrinsicGapPeriod
  have he : (fun E => c*N E/hillEnergyCanonicalRootProduct q hq hr E) =
      (fun E => c*(N E/hillEnergyCanonicalRootProduct q hq hr E)) := by funext E; ring
  rw [he,circleIntegral.integral_const_mul]
  ring

theorem hillIntrinsicGapPeriod_add (k : ℕ) (hk : 1 ≤ k) (N M : ℂ → ℂ)
    (hN : AnalyticOnNhd ℂ N univ) (hM : AnalyticOnNhd ℂ M univ) :
    hillIntrinsicGapPeriod q hq hr k (fun E => N E+M E) =
      hillIntrinsicGapPeriod q hq hr k N+hillIntrinsicGapPeriod q hq hr k M := by
  unfold hillIntrinsicGapPeriod
  simp_rw [add_div]
  rw [circleIntegral.integral_add (hillIntrinsicGapPeriod_circleIntegrable q hq hr k hk N hN)
    (hillIntrinsicGapPeriod_circleIntegrable q hq hr k hk M hM)]
  ring

theorem analyticOnNhd_hillAbelianHilbertPsi_rootUpdate_energy (n m : ℕ) (a : Coeff 2) (s : ℂ) :
    AnalyticOnNhd ℂ (fun E => hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,s))) univ := by
  intro E _
  exact (analyticOnNhd_hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,s)) (mem_univ _)).comp
    (f := fun E : ℂ => (E,hillAbelianRootUpdate m (a,s))) (analyticAt_id.prod analyticAt_const)

end NLS.KdV
