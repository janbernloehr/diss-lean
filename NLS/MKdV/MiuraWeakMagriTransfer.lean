import NLS.MKdV.SobolevMiuraDifferential
import NLS.Poisson.HillWeakMagri

/-! # Miura transfers the actual H¹ Gardner bracket to the weak Hill Magri bivector

The original input u is an arbitrary complex H¹ profile. The test
Hilbert gradients carry one further derivative, encoded by actual H¹
pairs (f,f') and (g,g'). Integration by parts proves the transfer directly
at this regularity, without inserting a derivative of the L² potential.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.MKdV

theorem miuraWeakMagriTransfer (u f df g dg : ScalarDomain 2)
    (hf : periodOneDerivative f = scalarInclusion df) (hg : periodOneDerivative g = scalarInclusion dg) :
    reflectedHilbertPairing (scalarInclusion (-df+(2 : ℂ) • periodOneSobolevProduct u f))
      (periodOneDerivative (-dg+(2 : ℂ) • periodOneSobolevProduct u g)) =
        hillWeakMagriBivector (sobolevMiuraUnitPotential u) f df g dg := by
  have hfirst : reflectedHilbertPairing (scalarInclusion df) (periodOneL2Multiplication g (periodOneDerivative u)) =
      reflectedHilbertPairing (periodOneDerivative u) (scalarInclusion (periodOneSobolevProduct df g)) := by
    rw [reflectedHilbertPairing_L2Multiplication,periodOneL2Multiplication_inclusion,
      periodOneSobolevProduct_comm g df,reflectedHilbertPairing_comm]
  have hlast : reflectedHilbertPairing (scalarInclusion (periodOneSobolevProduct u f))
      (periodOneL2Multiplication u (scalarInclusion dg)) =
      reflectedHilbertPairing (scalarInclusion (periodOneSobolevProduct u u))
        (scalarInclusion (periodOneSobolevProduct f dg)) := by
    have h := reflectedHilbertPairing_product_cross f u u (scalarInclusion dg)
    rw [periodOneL2Multiplication_inclusion,periodOneSobolevProduct_comm f u,
      reflectedHilbertPairing_comm (scalarInclusion (periodOneSobolevProduct f dg))] at h
    exact h.symm
  have hparts := reflectedHilbertPairing_product_derivative u f df dg hf
  have hsquare := reflectedHilbertPairing_square_product_derivative u f df g dg hf hg
  rw [sobolevMiuraUnitPotential_eq_product]
  unfold hillWeakMagriBivector
  simp only [map_add,map_neg,map_smul,smul_apply,add_apply,neg_apply,smul_eq_mul,
    map_sub]
  rw [periodOneDerivative_product_L2,hg]
  simp only [map_add]
  rw [hfirst,hlast]
  linear_combination -2*hparts+2*hsquare

end NLS.MKdV
