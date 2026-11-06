import NLS.ZakharovShabat.SobolevOddHamiltonianReal
import NLS.ZakharovShabat.SourceHigherActionIsospectral

/-! # Spectral invariance of the native odd Hamiltonian hierarchy

The full-domain higher-action trace identifies the independently defined
physical Hamiltonians. No smoothness or finite-gap premise is imposed.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- Every native odd Hamiltonian is constant on actual periodic isospectral sets. -/
theorem sobolevOddHamiltonian_eq_of_isospectral (m : ℕ) (hm : 1 ≤ m)
    (a b : realTypeHigherSobolevSourceLocus m)
    (h : (⟨higherSobolevSourceInclusion m b.val,b.property⟩ : realTypeSourceSubmodule 2) ∈
      sourceIsospectralSet (by simp) ⟨higherSobolevSourceInclusion m a.val,a.property⟩) :
    sobolevOddHamiltonian m hm b.val = sobolevOddHamiltonian m hm a.val := by
  rw [sobolevOddHamiltonian_eq_real_action_sum,sobolevOddHamiltonian_eq_real_action_sum]
  congr 2
  apply tsum_congr
  intro n
  exact sourceRealHigherAction_eq_of_isospectral (by simp) (by norm_num) _ _ h n (2*m)

/-- Equality of the entire original Dirac discriminants suffices at every
native Sobolev order, including arbitrary nonsmooth inputs. -/
theorem sobolevOddHamiltonian_eq_of_discriminant_eq (m : ℕ) (hm : 1 ≤ m)
    (a b : realTypeHigherSobolevSourceLocus m)
    (h : canonicalDiscriminant (by simp)
        (periodOnePotential (higherSobolevSourceInclusion m b.val)) =
      canonicalDiscriminant (by simp)
        (periodOnePotential (higherSobolevSourceInclusion m a.val))) :
    sobolevOddHamiltonian m hm b.val = sobolevOddHamiltonian m hm a.val := by
  apply sobolevOddHamiltonian_eq_of_isospectral m hm a b
  exact (mem_sourceIsospectralSet_iff_discriminant_eq (by simp) (by norm_num) _ _).mpr h

end NLS.ZakharovShabat
