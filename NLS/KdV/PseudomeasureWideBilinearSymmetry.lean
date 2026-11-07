import NLS.KdV.PseudomeasureWideReconstruction
import NLS.KdV.PseudomeasureBilinearSymmetry

/-! Physical bilinear Green symmetry on the entire printed 12n strip. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- Pairing the finite residual with reconstruction gives the off-diagonal two-mode pairing. -/
theorem wideEndpointHillPairing_residual (u v : ℂ × ℂ) :
    singularHillPairing (wideEndpointHillResonantResidual r hr hr1 n hn z hz q hs u)
      (wideEndpointHillReconstruct r hr hr1 n hn z hz q hs v) =
      (wideEndpointHillReducedOperator r hr hr1 n hn z hz q hs u).1*v.2 +
        (wideEndpointHillReducedOperator r hr hr1 n hn z hz q hs u).2*v.1 := by
  unfold wideEndpointHillResonantResidual
  rw [endpointHillH1Modes_eq, map_add, map_smul, map_smul,
    singularHillPairing_add_left, singularHillPairing_smul_left, singularHillPairing_smul_left,
    singularHillPairing_mode, singularHillPairing_mode]
  have hp := congrArg Prod.fst (endpointHillH1Coordinates_wideReconstruct r hr hr1 n hn z hz q hs v)
  have hm := congrArg Prod.snd (endpointHillH1Coordinates_wideReconstruct r hr hr1 n hn z hz q hs v)
  change (wideEndpointHillReconstruct r hr hr1 n hn z hz q hs v).val (mode (-(n:ℤ))) = v.1 at hp
  change (wideEndpointHillReconstruct r hr hr1 n hn z hz q hs v).val (mode (-(-(n:ℤ)))) = v.2 at hm
  simp only [neg_neg] at hm
  rw [hp, hm]

/-- The effective endpoint matrix inherits the physical bilinear Green symmetry. -/
theorem wideEndpointHillReduced_bilinearSymmetry (u v : ℂ × ℂ) :
    (wideEndpointHillReducedOperator r hr hr1 n hn z hz q hs u).1*v.2 +
      (wideEndpointHillReducedOperator r hr hr1 n hn z hz q hs u).2*v.1 =
    (wideEndpointHillReducedOperator r hr hr1 n hn z hz q hs v).1*u.2 +
      (wideEndpointHillReducedOperator r hr hr1 n hn z hz q hs v).2*u.1 := by
  have he := singularHillPencil_bilinear (endpointHillHminusOne SpectralWeight.one r hr1 q) z
    (wideEndpointHillReconstruct r hr hr1 n hn z hz q hs u)
    (wideEndpointHillReconstruct r hr hr1 n hn z hz q hs v)
  rw [wideEndpointHillReconstruct_residual_equation, wideEndpointHillReconstruct_residual_equation,
    wideEndpointHillPairing_residual, wideEndpointHillPairing_residual] at he
  exact he

/-- Equality of the actual diagonal corrections, with no reality assumption on q. -/
theorem wideEndpointHillEffectivePotential_diagonals_eq :
    (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0)).val n =
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1)).val (-(n:ℤ)) := by
  have he := wideEndpointHillReduced_bilinearSymmetry r hr hr1 n hn z hz q hs (1,0) (0,1)
  simp only [mul_one, mul_zero, add_zero, zero_add] at he
  change (z-(freeHillValue n:ℂ))*1 -
    (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0)).val n =
      (z-(freeHillValue n:ℂ))*1 -
        (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1)).val (-(n:ℤ)) at he
  linear_combination -he

end NLS.KdV
