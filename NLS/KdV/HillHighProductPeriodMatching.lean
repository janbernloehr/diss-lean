import NLS.KdV.HillProductPeriodUniformLimit
import NLS.KdV.HillHighIntrinsicPeriodComparison

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillHighAbelianProductComplexPeriod_eq_intrinsic_physical
    (Ncut : ℕ) (hNcut : 1 ≤ Ncut) (B D : ℝ) (hc : HillComplexTailPeriodControl h0q h0r Ncut B D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B) (n k : ℕ) (hk : Ncut ≤ k) (a : Coeff 2) :
    hillAbelianProductComplexPeriod 0 h0q h0r n k (a,SpectralWeight.one.toCoeff q) =
      (2*(Real.pi:ℂ))⁻¹ * ∮ E in C((hillRealGapCenter q hq hr k : ℂ),
        hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        hillAbelianHilbertProduct n (E,a)/hillEnergyCanonicalRootProduct q hq hr E := by
  have hk1 : 1 ≤ k := hNcut.trans hk
  have hN : AnalyticOnNhd ℂ (fun E => hillAbelianHilbertProduct n (E,a)) univ := by
    intro E _
    exact (analyticOnNhd_hillAbelianHilbertProduct n (E,a) (mem_univ _)).comp
      (f := fun E : ℂ => (E,a)) (analyticAt_id.prod analyticAt_const)
  unfold hillAbelianProductComplexPeriod
  congr 1
  calc
    _ = ∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
      hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      hillAbelianHilbertProduct n (E,a)/hillEnergyCanonicalRootProduct q hq hr E := by
        apply circleIntegral.integral_congr
          (add_nonneg (hillRealGapContour_geometry 0 h0q h0r k hk1).1
            (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1.le)
        intro E hE
        dsimp only []
        rw [(hillHighFreeGapContour_physical_root_matching h0q h0r Ncut hNcut B D hc q hq hr hp k hk E hE).2]
    _ = _ := hillHighPhysicalContour_period_eq_free_contour h0q h0r Ncut hNcut B D hc q hq hr hp k hk _ hN

end NLS.KdV
