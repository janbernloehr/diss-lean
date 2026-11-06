import NLS.KdV.HillDiscriminantCotangentModes
import NLS.Poisson.HminusGardnerHilbertRestriction
import NLS.SequenceSpaces.InsertionSingle

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Physical even-index insertion of original unit-period Hilbert directions. -/
def hillNativeHilbertDirection : Coeff 2 →L[ℂ] Coeff 2 :=
  (Coeff.insertIsometry (Coeff.parityEmbedding 0)).toContinuousLinearMap

/-- Literal unit-mode values identify the original native physical
differential with the restriction of its genuine H-minus-one cotangent.
The original even-index embedding, physical sign and 2*pi normalization
are retained in this equality of bounded differentials. -/
theorem hillPhysicalDifferential_eq_hminusRestriction
    (L : Coeff 2 →L[ℂ] ℂ) (f : Curve ℂ) (a : WeightedCoeff (Weight.sobolev 1) 2)
    (ha : ∀ k : ℤ, a.val k=Fourier.unitFourierCoefficient (extend f) k)
    (hL : ∀ n : ℤ, L (lp.single 2 (2*n) 1)=hillPhysicalDirectionPairing (lp.single 2 (2*n) 1) f) :
    L.comp hillNativeHilbertDirection=
      (WeightedCoeff.sobolevBilinearPairing 1 a).comp NLS.Poisson.hilbertToHminus := by
  apply NLS.Poisson.hilbertDifferential_eq_hminusRestriction_of_modes
  intro n
  change L (Coeff.insert (Coeff.parityEmbedding 0) (lp.single 2 n 1))=a.val (-n)
  rw [Coeff.insert_single,Coeff.parityEmbedding_apply,add_zero,hL n,ha (-n),hillPhysicalDirectionPairing_apply]
  unfold Fourier.unitFourierCoefficient
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_single_lower_ae (2*n)] with x hx
  rw [hx,show -(2*(-n))=2*n by ring,mul_comm]

end NLS.KdV
