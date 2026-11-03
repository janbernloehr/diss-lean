import NLS.KdV.HillContourHilbertProductSeparation
import NLS.KdV.HillScaledFreeContourQuotient

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillAbelianHilbertPsi_zero_eq_free (n : ℕ) (E : ℂ) :
    hillAbelianHilbertPsi n (E,0) = hillAbelianPsiCandidate hillFreeGapRoot n E := by
  apply hillAbelianHilbertPsi_eq_real_candidate
  intro j
  simp only [hillFreeGapRoot,lp.coeFn_zero,Pi.zero_apply,mul_zero,add_zero]

theorem hillAbelianHilbertPsi_contour_separation (n k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) (a : Coeff 2) :
    hillAbelianHilbertPsi n (E,a) = hillAbelianPsiCandidate hillFreeGapRoot n E *
      hilbertWeightedProduct (hillFreeContourWeight hq hr n k hk E hE) a := by
  rw [← hillAbelianHilbertPsi_zero_eq_free n E,hillAbelianHilbertPsi,
    hillAbelianHilbertProduct_contour_separation hq hr n k hk E hE a,hillAbelianHilbertPsi]
  ring

theorem norm_scaled_hillAbelianHilbertPsi_free_root_le (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hnk : n ≠ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) (a : Coeff 2) :
    ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 hq hr E)‖ ≤
      (4/(k : ℝ))*Real.exp ((8/Real.pi^2)*‖a‖) := by
  rw [hillAbelianHilbertPsi_contour_separation hq hr n k hk E hE a]
  have he : (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      ((hillAbelianPsiCandidate hillFreeGapRoot n E*
        hilbertWeightedProduct (hillFreeContourWeight hq hr n k hk E hE) a)/
          hillEnergyCanonicalRootProduct 0 hq hr E) =
      ((((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianPsiCandidate hillFreeGapRoot n E/hillEnergyCanonicalRootProduct 0 hq hr E))*
          hilbertWeightedProduct (hillFreeContourWeight hq hr n k hk E hE) a := by ring
  rw [he,norm_mul]
  exact mul_le_mul (norm_scaled_hillFreeAbelianQuotient_on_contour hq hr n k hn hk hnk E hE)
    (norm_hilbertWeightedProduct_hillFreeContour_le hq hr n k hk E hE a)
    (norm_nonneg _) (by positivity)

end NLS.KdV
