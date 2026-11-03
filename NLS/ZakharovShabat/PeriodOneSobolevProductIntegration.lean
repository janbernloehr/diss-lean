import NLS.ZakharovShabat.PeriodOneL2Multiplication

/-! # Integration by parts for weak products on the physical unit circle -/
noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem reflectedHilbertPairing_product_cross (u f g : ScalarDomain 2) (h : Coeff 2) :
    reflectedHilbertPairing (periodOneL2Multiplication u h) (scalarInclusion (periodOneSobolevProduct f g)) =
      reflectedHilbertPairing (scalarInclusion (periodOneSobolevProduct u f)) (periodOneL2Multiplication g h) := by
  rw [← reflectedHilbertPairing_L2Multiplication,periodOneL2Multiplication_inclusion,
    periodOneSobolevProduct_assoc,reflectedHilbertPairing_comm]
  rw [reflectedHilbertPairing_L2Multiplication,periodOneL2Multiplication_inclusion,
    periodOneSobolevProduct_comm g]

theorem reflectedHilbertPairing_product_derivative (u f df g : ScalarDomain 2)
    (hf : periodOneDerivative f = scalarInclusion df) :
    reflectedHilbertPairing (scalarInclusion (periodOneSobolevProduct u f)) (periodOneDerivative g) =
      -reflectedHilbertPairing (periodOneDerivative u) (scalarInclusion (periodOneSobolevProduct f g))-
        reflectedHilbertPairing (scalarInclusion df) (periodOneL2Multiplication u (scalarInclusion g)) := by
  rw [reflectedHilbertPairing_periodOneDerivative,periodOneDerivative_product_L2,hf]
  rw [map_add,add_apply,← reflectedHilbertPairing_L2Multiplication f,
    ← reflectedHilbertPairing_L2Multiplication u,periodOneL2Multiplication_inclusion]
  ring

/-- Integration by parts in the H¹ products u² and f*g retains the
rough L² derivative of u. No smoothness of the original H¹ input is added. -/
theorem reflectedHilbertPairing_square_product_derivative (u f df g dg : ScalarDomain 2)
    (hf : periodOneDerivative f = scalarInclusion df) (hg : periodOneDerivative g = scalarInclusion dg) :
    2*reflectedHilbertPairing (scalarInclusion (periodOneSobolevProduct u f))
      (periodOneL2Multiplication g (periodOneDerivative u)) =
        -reflectedHilbertPairing (scalarInclusion (periodOneSobolevProduct u u))
          (scalarInclusion (periodOneSobolevProduct df g))-
        reflectedHilbertPairing (scalarInclusion (periodOneSobolevProduct u u))
          (scalarInclusion (periodOneSobolevProduct f dg)) := by
  have h := reflectedHilbertPairing_periodOneDerivative (periodOneSobolevProduct u u) (periodOneSobolevProduct f g)
  rw [periodOneDerivative_product_L2,periodOneDerivative_product_L2,hf,hg,
    periodOneL2Multiplication_inclusion,periodOneL2Multiplication_inclusion,
    periodOneSobolevProduct_comm g df] at h
  simp only [map_add,add_apply] at h
  rw [reflectedHilbertPairing_product_cross] at h
  linear_combination h

end NLS.ZakharovShabat
