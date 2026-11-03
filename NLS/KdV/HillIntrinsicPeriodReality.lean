import NLS.KdV.HillCanonicalRootConjugation
import NLS.KdV.HillGapBoxPeriodNonvanishing
import NLS.ComplexAnalysis.RealCircleIntegralReflection

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillIntrinsicGapPeriod (k : ℕ) (N : ℂ → ℂ) : ℂ :=
  (2*(Real.pi:ℂ))⁻¹ * ∮ E in C((hillRealGapCenter q hq hr k : ℂ),
    hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
    N E/hillEnergyCanonicalRootProduct q hq hr E

theorem hillIntrinsicGapPeriod_im_eq_zero (k : ℕ) (hk : 1 ≤ k) (N : ℂ → ℂ)
    (hN : ∀ E : ℂ, N (conj E) = conj (N E)) :
    (hillIntrinsicGapPeriod q hq hr k N).im = 0 := by
  have hR : 0 < hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k :=
    add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
      (hillRealGapContour_geometry q hq hr k hk).2.1
  have hi := circleIntegral_im_eq_zero_of_anti_conj
    (fun E => N E/hillEnergyCanonicalRootProduct q hq hr E) (hillRealGapCenter q hq hr k) _ hR (by
      intro E hE
      rw [hN E,hillEnergyCanonicalRootProduct_conj q hq hr E
        (hillRealGapContour_sphere_subset q hq hr k hk hE)]
      simp only [div_neg,map_div₀])
  simp [hillIntrinsicGapPeriod,Complex.mul_im,Complex.inv_im,hi]

end NLS.KdV
