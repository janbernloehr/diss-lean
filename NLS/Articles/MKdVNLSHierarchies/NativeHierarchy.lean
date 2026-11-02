import NLS.MKdV.NativeMiuraHillGradient
import NLS.ZakharovShabat.SobolevOddHamiltonianAllOrders
import NLS.Articles.MKdVNLSHierarchies.SharpEvenVanishing

/-! # Native-domain Hamiltonian and flow comparisons

K_m is independently constructed on its full complex H^(m-1) domain. The
source spectral identification is still separate from these precise native
physical Hamiltonian and weak-flow statements.
-/
noncomputable section
open NLS.MKdV NLS.ZakharovShabat NLS.Fourier
namespace NLS.Articles.MKdVNLSHierarchies

/-- The odd identity in Proposition 6 on exactly complex H^(m-1), including
the L² mass endpoint. The scalar side is independently constructed from the
scalar Hill density, not defined by the identity being asserted. -/
theorem proposition6_native_miura (m : ℕ) (hm : 1 ≤ m) (u : ScalarSobolev (m-1)) :
    sharpOddNLSHamiltonian (m-1) (u,u) = 2*nativeMiuraHillHamiltonian (m-1) u := by
  obtain ⟨s,rfl⟩ : ∃ s, m = s+1 := ⟨m-1, by omega⟩
  change sharpOddNLSHamiltonian s (u,u) = 2*nativeMiuraHillHamiltonian s u
  by_cases hs : 1 ≤ s
  · rw [sharpOddNLSHamiltonian,dif_pos hs]
    exact nativeMiuraHillHamiltonian_odd_restriction s hs u
  · have hz : s = 0 := by omega
    subst s
    rw [sharpOddNLSHamiltonian,dif_neg (by omega : ¬1 ≤ (0 : ℕ))]
    exact nativeMiuraHillHamiltonian_mass_restriction u

/-- Both Theorem 1 clauses for the native scalar Hill/Miura Hamiltonian:
all complex H^m inputs, and Gardner's actual distribution derivative of the
actual Frechet gradient constructed on H^(m-1). -/
theorem theorem1_native_miura_hierarchy (m : ℕ) (hm : 1 ≤ m) (u : ScalarSobolev m) :
    sobolevEvenHamiltonian m hm (u,u) = 0 ∧
      (periodOneSobolevDistribution (-(m : ℝ)) (sobolevEvenHierarchyVectorField m hm (u,u)).1,
        periodOneSobolevDistribution (-(m : ℝ)) (sobolevEvenHierarchyVectorField m hm (u,u)).2) =
        (nativeMiuraHillVectorField (m-1) (hierarchySobolevInclusion m (m-1) (by omega) u),
          nativeMiuraHillVectorField (m-1) (hierarchySobolevInclusion m (m-1) (by omega) u)) := by
  constructor
  · exact theorem1_even_vanishing_sharp m hm u
  · obtain ⟨s,rfl⟩ : ∃ s, m = s+1 := ⟨m-1, by omega⟩
    exact nativeMiuraHillFlowRestriction s u

end NLS.Articles.MKdVNLSHierarchies
