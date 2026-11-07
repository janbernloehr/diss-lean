import NLS.ZakharovShabat.SobolevHierarchyReflectionNonlocal

/-! # Proposition 11(iii), corrected on its entire original complex domain

The gradient at level 2m remains its actual original L2 gradient. The lower
gradient has its proved continuous physical representative and genuine spatial
derivative almost everywhere. The nonlocal term is +2*i*(J*phi) times the
actual zero-initial physical integral. Both printed reflection signs are kept.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

theorem proposition11_iii_corrected (m : ℕ) (hm : 1 ≤ m) (ε : ℂ) (hε : ε=1 ∨ ε = -1)
    (ab : SobolevSource (2*m-1)) (hT : hierarchyMidpointReflection (2*m-1) ab=ε • ab) :
    ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
      (I*unitL2SynthesisEquiv (sobolevNLSHierarchyGradient (2*m-1) (2*m) ab).1 x,
       -I*unitL2SynthesisEquiv (sobolevNLSHierarchyGradient (2*m-1) (2*m) ab).2 x) =
        ((deriv (hierarchyPhysicalGradient (2*m-1) (2*m-1) ab) x).1+
          2*I*(hierarchyPhysicalPotential (2*m-1) ab x).2*
            (∫ y in (0:ℝ)..x, hierarchyPhysicalRPairing (2*m-1) (2*m-1) ab y),
         (deriv (hierarchyPhysicalGradient (2*m-1) (2*m-1) ab) x).2-
          2*I*(hierarchyPhysicalPotential (2*m-1) ab x).1*
            (∫ y in (0:ℝ)..x, hierarchyPhysicalRPairing (2*m-1) (2*m-1) ab y)) := by
  revert ab
  rw [show 2*m-1=2*(m-1)+1 by omega]
  intro ab hT
  simpa only [show 2*m=2*(m-1)+2 by omega] using hierarchyReflection_physical_nonlocal (m-1) ε hε ab hT

end NLS.Articles.MKdVNLSHierarchies
