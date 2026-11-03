import NLS.ZakharovShabat.SourceComponentSwapHamiltonians
import NLS.ZakharovShabat.SourceWeightedComponentSwap
import NLS.ZakharovShabat.SourceSobolevFourthHamiltonian
import NLS.ZakharovShabat.SourceWeightedFiniteGapEquality

/-! # Physical H₄ is antisymmetric on its full native fractional domain

The finite-gap trace parity extends by density in the original H^(3/2)
norm. Both sides retain the independently defined physical Hamiltonian.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Unsigned component exchange changes the sign of physical H₄ on every
original real H^(3/2) source, including infinitely many open gaps. -/
theorem sourceSobolevFourthHamiltonian_componentSwap (a : NativeFourthSobolevSource) :
    sourceSobolevFourthHamiltonian (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) =
      -sourceSobolevFourthHamiltonian a := by
  apply eq_of_continuous_weighted_finiteGap (by simp) (by norm_num)
    fourthSobolevSpectralWeight
    (fun b => sourceSobolevFourthHamiltonian (weightedRealSourceComponentSwap fourthSobolevSpectralWeight b))
    (fun b => -sourceSobolevFourthHamiltonian b)
    (continuous_sourceSobolevFourthHamiltonian.comp
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight).continuous)
    continuous_sourceSobolevFourthHamiltonian.neg _ a
  intro b hf
  have hs : originalWeightedRealSource fourthSobolevSpectralWeight
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight b) ∈
      sourceFiniteGapLocus (by simp) (by norm_num) := by
    rw [originalWeightedRealSource_componentSwap]
    exact realSourceComponentSwap_mem_finiteGap (by simp) (by norm_num) _ hf
  rw [sourceSobolevFourthHamiltonian_eq_finiteGap _ hs,
    sourceSobolevFourthHamiltonian_eq_finiteGap _ hf]
  simpa only [originalWeightedRealSource_componentSwap] using
    sourceFiniteGapFourthHamiltonian_componentSwap (by simp) (by norm_num) _ hf

/-- The genuine real-valued physical Hamiltonian has the same full-domain parity. -/
theorem sourceRealSobolevFourthHamiltonian_componentSwap (a : NativeFourthSobolevSource) :
    sourceRealSobolevFourthHamiltonian (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) =
      -sourceRealSobolevFourthHamiltonian a :=
  congrArg Complex.re (sourceSobolevFourthHamiltonian_componentSwap a)

/-- The actual mKdV diagonal is a zero level of physical H₄ throughout H^(3/2). -/
theorem sourceSobolevFourthHamiltonian_eq_zero_of_diagonal
    (a : NativeFourthSobolevSource) (ha : a.val.fst = a.val.snd) :
    sourceSobolevFourthHamiltonian a = 0 := by
  have hs := sourceSobolevFourthHamiltonian_componentSwap a
  rw [(weightedRealSourceComponentSwap_eq_self_iff fourthSobolevSpectralWeight a).mpr ha] at hs
  have he := congrArg Complex.re hs
  have hi := congrArg Complex.im hs
  apply Complex.ext <;> simp only [Complex.neg_re,Complex.neg_im,Complex.zero_re,Complex.zero_im] at * <;> linarith

end NLS.ZakharovShabat
