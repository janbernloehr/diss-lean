import NLS.MKdV.SobolevMiuraMagriCanonical
import NLS.MKdV.MiuraNativeActionFlowChainRule

/-! # Poisson transfer needed for the independent mKdV angles

The original Miura map transfers the physical Gardner bracket to the
weak Hill Magri bracket on the entire complex H¹ domain. Native action
flow tangents retain the actual Gardner coefficients at every positive
Sobolev order. These results supply analytic prerequisites for Theorem
4(iii); they do not construct its independent mKdV angle family.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- The original complex H¹ Miura map is Poisson for actual Hill
functionals with H² gradients, with any actual pullback representatives. -/
theorem physical_Miura_Gardner_Magri_transfer (F G : Coeff 2 → ℂ) (a : ScalarDomain 2)
    (f g : ScalarSobolev 2)
    (hF : HasFDerivAt F (reflectedHilbertPairing (scalarInclusion (sobolevHillTestInclusion f)))
      (sobolevMiuraUnitPotential a))
    (hG : HasFDerivAt G (reflectedHilbertPairing (scalarInclusion (sobolevHillTestInclusion g)))
      (sobolevMiuraUnitPotential a))
    (P : SobolevGardnerGradientAt (fun b => F (sobolevMiuraUnitPotential b)) a)
    (Q : SobolevGardnerGradientAt (fun b => G (sobolevMiuraUnitPotential b)) a) :
    P.bracket Q = hillSobolevMagriBivector (sobolevMiuraUnitPotential a) f g :=
  sobolevMiura_bracket_eq_Magri_of_gradients F G a f g hF hG P Q

/-- The actual original action flow is differentiable in each positive
native Sobolev norm and has the physical Gardner field as its L² tangent. -/
theorem physical_action_flow_native_Gardner_tangent (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n) :
    HasDerivAt (miuraActionFlow s a.val (fun j => a.property j) n)
        (miuraNativeActionVelocity s a n) 0 ∧
      hierarchySobolevJetL2 s 0 (Nat.zero_le _) (miuraNativeActionVelocity s a n) =
        l2GardnerDirection (miuraL2Action n) (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val) :=
  ⟨hasDerivAt_miuraActionFlow_native_zero s hs a n hn,
    miuraNativeActionVelocity_L2_Gardner s hs a n hn⟩

end NLS.Articles.MKdVNLSHierarchies
