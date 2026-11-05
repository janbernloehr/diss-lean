import NLS.MKdV.MiuraWeakMagriTransfer
import NLS.Poisson.SobolevGardnerGradient

/-! # Canonical Miura bracket transfer for actual differentiable functionals

Every original complex H¹ input is included. Actual H² Hill gradients
pull back to actual H¹ Gardner gradients. The physical Gardner bracket
of the pulled-back functionals is the independently defined weak Magri
bivector of their original Hill gradients. It is independent of gradient
representatives and of the chosen Miura representative of the potential.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.MKdV

def hillSobolevMagriBivector (q : Coeff 2) (f g : ScalarSobolev 2) : ℂ :=
  hillWeakMagriBivector q (sobolevHillTestInclusion f) (sobolevHillTestDerivative f)
    (sobolevHillTestInclusion g) (sobolevHillTestDerivative g)

def miuraSobolevPullbackGradient (F : Coeff 2 → ℂ) (a : ScalarDomain 2) (f : ScalarSobolev 2)
    (hF : HasFDerivAt F (reflectedHilbertPairing (scalarInclusion (sobolevHillTestInclusion f)))
      (sobolevMiuraUnitPotential a)) :
    SobolevGardnerGradientAt (fun b => F (sobolevMiuraUnitPotential b)) a where
  gradient := sobolevMiuraAdjoint a f
  hasFDerivAt := hasFDerivAt_sobolevMiura_pullback F a f hF

theorem sobolevMiuraPullbackGradient_bracket_eq_Magri (F G : Coeff 2 → ℂ) (a : ScalarDomain 2)
    (f g : ScalarSobolev 2)
    (hF : HasFDerivAt F (reflectedHilbertPairing (scalarInclusion (sobolevHillTestInclusion f)))
      (sobolevMiuraUnitPotential a))
    (hG : HasFDerivAt G (reflectedHilbertPairing (scalarInclusion (sobolevHillTestInclusion g)))
      (sobolevMiuraUnitPotential a)) :
    (miuraSobolevPullbackGradient F a f hF).bracket (miuraSobolevPullbackGradient G a g hG) =
      hillSobolevMagriBivector (sobolevMiuraUnitPotential a) f g := by
  exact miuraWeakMagriTransfer a (sobolevHillTestInclusion f) (sobolevHillTestDerivative f)
    (sobolevHillTestInclusion g) (sobolevHillTestDerivative g)
    (scalarInclusion_sobolevHillTestDerivative f).symm (scalarInclusion_sobolevHillTestDerivative g).symm

/-- Any actual H¹ gradients representing the two pulled-back
functionals give the same physical Magri bracket. -/
theorem sobolevMiura_bracket_eq_Magri_of_gradients (F G : Coeff 2 → ℂ) (a : ScalarDomain 2)
    (f g : ScalarSobolev 2)
    (hF : HasFDerivAt F (reflectedHilbertPairing (scalarInclusion (sobolevHillTestInclusion f)))
      (sobolevMiuraUnitPotential a))
    (hG : HasFDerivAt G (reflectedHilbertPairing (scalarInclusion (sobolevHillTestInclusion g)))
      (sobolevMiuraUnitPotential a))
    (P : SobolevGardnerGradientAt (fun b => F (sobolevMiuraUnitPotential b)) a)
    (Q : SobolevGardnerGradientAt (fun b => G (sobolevMiuraUnitPotential b)) a) :
    P.bracket Q = hillSobolevMagriBivector (sobolevMiuraUnitPotential a) f g := by
  rw [P.bracket_choice_independent (miuraSobolevPullbackGradient F a f hF) Q
    (miuraSobolevPullbackGradient G a g hG)]
  exact sobolevMiuraPullbackGradient_bracket_eq_Magri F G a f g hF hG

theorem sobolevMiura_Magri_independent_of_representative (a b : ScalarDomain 2)
    (hab : sobolevMiuraUnitPotential a = sobolevMiuraUnitPotential b) (f g : ScalarSobolev 2) :
    reflectedHilbertPairing (scalarInclusion (sobolevMiuraAdjoint a f)) (periodOneDerivative (sobolevMiuraAdjoint a g)) =
      reflectedHilbertPairing (scalarInclusion (sobolevMiuraAdjoint b f)) (periodOneDerivative (sobolevMiuraAdjoint b g)) := by
  have h (u : ScalarDomain 2) := miuraWeakMagriTransfer u
    (sobolevHillTestInclusion f) (sobolevHillTestDerivative f)
    (sobolevHillTestInclusion g) (sobolevHillTestDerivative g)
    (scalarInclusion_sobolevHillTestDerivative f).symm (scalarInclusion_sobolevHillTestDerivative g).symm
  exact (h a).trans ((congrArg (fun q => hillSobolevMagriBivector q f g) hab).trans (h b).symm)

end NLS.MKdV
