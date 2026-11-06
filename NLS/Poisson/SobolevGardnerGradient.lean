import NLS.ZakharovShabat.SourceSobolevMomentumDifferential
import NLS.Poisson.SourceCoordinateBrackets

/-! # Actual H¹ Gardner gradients for functionals defined on H¹

The physical bracket only requires an H¹ Hilbert gradient. A functional
on H¹ need not extend to L². Finite physical Fourier variations determine
the Hilbert gradient uniquely from the actual complex differential.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Poisson

structure SobolevGardnerGradientAt (F : ScalarDomain 2 → ℂ) (a : ScalarDomain 2) where
  gradient : ScalarDomain 2
  hasFDerivAt : HasFDerivAt F ((reflectedHilbertPairing (scalarInclusion gradient)).comp scalarInclusion) a

namespace SobolevGardnerGradientAt
variable {F G : ScalarDomain 2 → ℂ} {a : ScalarDomain 2}

theorem gradient_unique (P Q : SobolevGardnerGradientAt F a) : P.gradient = Q.gradient := by
  have he := P.hasFDerivAt.unique Q.hasFDerivAt
  apply Subtype.ext
  funext n
  have hv := congrArg (fun L : ScalarDomain 2 →L[ℂ] ℂ => L (scalarMode (-n) 1)) he
  change reflectedHilbertPairing (scalarInclusion P.gradient) (scalarInclusion (scalarMode (-n) 1)) =
    reflectedHilbertPairing (scalarInclusion Q.gradient) (scalarInclusion (scalarMode (-n) 1)) at hv
  rw [scalarInclusion_scalarMode,reflectedHilbertPairing_comm _ (lp.single 2 (-n) 1),
    reflectedHilbertPairing_comm _ (lp.single 2 (-n) 1),
    reflectedHilbertPairing_single_left,reflectedHilbertPairing_single_left] at hv
  simpa only [neg_neg,one_mul,scalarInclusion_apply] using hv

def bracket (P : SobolevGardnerGradientAt F a) (Q : SobolevGardnerGradientAt G a) : ℂ :=
  reflectedHilbertPairing (scalarInclusion P.gradient) (periodOneDerivative Q.gradient)

theorem bracket_antisymm (P : SobolevGardnerGradientAt F a) (Q : SobolevGardnerGradientAt G a) :
    P.bracket Q = -Q.bracket P := by
  rw [bracket,bracket,reflectedHilbertPairing_periodOneDerivative,reflectedHilbertPairing_comm]

theorem bracket_choice_independent (P P' : SobolevGardnerGradientAt F a)
    (Q Q' : SobolevGardnerGradientAt G a) : P.bracket Q = P'.bracket Q' := by
  unfold bracket
  rw [P.gradient_unique P',Q.gradient_unique Q']

end SobolevGardnerGradientAt
end NLS.Poisson
