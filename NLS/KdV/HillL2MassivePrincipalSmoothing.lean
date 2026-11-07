import NLS.KdV.HillSpectralCoreFourierPrincipal
import NLS.SequenceSpaces.PeriodOneMassSobolevInverse
import NLS.SequenceSpaces.SignedOrderHalfFourierEquiv
import NLS.SequenceSpaces.SignedSobolevPositiveEquivalence

/-! The original massive Hill principal minus the exact free Fourier
map has an explicit L2-to-native-H3/2 linear realization. The retained
signed principal identity supplies the original normalization. -/
noncomputable section
open Complex
namespace NLS.KdV

private def h1HalfFourier : ZakharovShabat.ScalarDomain 2 →L[ℂ]
    WeightedCoeff (Weight.signedSobolev (3/2)) 2 :=
  WeightedCoeff.weightedMultiplierCLM _ _ WeightedCoeff.halfFourierSymbol
    (1 / Real.sqrt (2 * Real.pi)) (by positivity) (by
      intro k
      have h : Weight.signedSobolev (3/2) k * ‖WeightedCoeff.halfFourierSymbol k‖ ≤
          (1 / Real.sqrt (2 * Real.pi)) * Weight.signedSobolev 1 k := by
        simpa only [show (1 : ℝ) + 1/2 = 3/2 by norm_num] using
          WeightedCoeff.halfFourierSymbol_signed_order_bound 1 k
      exact h.trans (mul_le_mul_of_nonneg_left (Weight.signedSobolev_le_sobolev 1 (by norm_num) k)
        (one_div_nonneg.mpr (Real.sqrt_nonneg _))))

def hillL2PrincipalFourierRemainder : Coeff 2 →L[ℂ] WeightedCoeff (Weight.signedSobolev (3/2)) 2 :=
  -(h1HalfFourier.comp (periodOneMassL2ToH1 0))

theorem hillL2PrincipalFourierRemainder_apply (q : Coeff 2) (k : ℤ) :
    (hillL2PrincipalFourierRemainder q).val k =
      -WeightedCoeff.halfFourierSymbol k * (periodOneMassSymbol 0 k)⁻¹ * q k := by
  change -(WeightedCoeff.halfFourierSymbol k * (periodOneMassL2ToH1 0 q).val k) = _
  rw [periodOneMassL2ToH1_apply]
  ring

theorem hillL2PrincipalFourierRemainder_eq_actual (q : Coeff 2) (k : ℤ) :
    (hillL2PrincipalFourierRemainder q).val k =
      (hillSpectralCoreDiracPrincipal (periodOneL2Inclusion q)).val k -
        WeightedCoeff.halfFourierSymbol k * q k := by
  rw [hillSpectralCoreDiracPrincipal_eq_halfFourier]
  change _ = WeightedCoeff.halfFourierSymbol k *
    ((periodOneL2Inclusion q).val k -
      (periodOneL2Inclusion (periodOneMassInverse 0 (periodOneL2Inclusion q))).val k) - _
  rw [periodOneL2Inclusion_apply, periodOneL2Inclusion_apply, periodOneMassInverse_apply,
    periodOneL2Inclusion_apply, hillL2PrincipalFourierRemainder_apply]
  ring

end NLS.KdV
