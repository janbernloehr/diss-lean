import NLS.KdV.HillPhysicalContourPeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillAbelianComplexPeriod_eq_intrinsic_physical
    (ε D : ℝ) (hc : HillComplexPeriodControl h0q h0r ε D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (n k : ℕ) (hk : 1 ≤ k) (a : Coeff 2) :
    hillAbelianComplexPeriod 0 h0q h0r n k (a,SpectralWeight.one.toCoeff q) =
      (2*(Real.pi:ℂ))⁻¹ * ∮ E in C((hillRealGapCenter q hq hr k : ℂ),
        hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct q hq hr E := by
  have hN : AnalyticOnNhd ℂ (fun E => hillAbelianHilbertPsi n (E,a)) univ := by
    intro E _
    exact (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).comp
      (f := fun E : ℂ => (E,a)) (analyticAt_id.prod analyticAt_const)
  unfold hillAbelianComplexPeriod
  congr 1
  calc
    _ = ∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
      hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct q hq hr E := by
        apply circleIntegral.integral_congr
          (add_nonneg (hillRealGapContour_geometry 0 h0q h0r k hk).1
            (hillRealGapContour_geometry 0 h0q h0r k hk).2.1.le)
        intro E hE
        dsimp only []
        rw [(hillFreeGapContour_physical_root_matching h0q h0r ε D hc q hq hr hp k hk E hE).2]
    _ = _ := hillPhysicalContour_period_eq_free_contour h0q h0r ε D hc q hq hr hp k hk _ hN

end NLS.KdV
