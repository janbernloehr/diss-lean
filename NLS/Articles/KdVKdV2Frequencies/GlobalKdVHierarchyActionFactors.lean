import NLS.Articles.KdVKdV2Frequencies.GlobalWeightedHamiltonianActionFactors
import NLS.KdV.NativeHillHierarchyReality

/-! # The full original KdV hierarchy as analytic functions of the actions

Every independently constructed physical H_m on H^m is evaluated at the
same global inverse. Analytic action factors use the original weighted l1
order 2m+1 and recover all raw real mean-zero h^(m+1/2) targets.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies

/-- Literal original positive products in the exact hierarchy action norm. -/
def hierarchyNativeActionSequence (m : ℕ)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) :
    WeightedCoeff (Weight.sobolev (2*(m : ℝ)+1)) 1 :=
  sobolevSignedActionSequence (2*(m : ℝ)+1) ((m : ℝ)+1/2) (by ring) z

theorem hierarchyNativeActionSequence_apply (m : ℕ)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) (n : ℤ) :
    (hierarchyNativeActionSequence m z).val n = if 0<n then z.val.val n*z.val.val (-n) else 0 :=
  sobolevSignedActionSequence_apply _ _ _ z n

namespace GlobalRoughAbelianForwardData

/-- The original physical H_m composed with the SAME fixed global inverse. -/
def birkhoffHillHierarchyHamiltonian (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) : ℝ :=
  (nativeHillHierarchyHamiltonian m (D.rawIntegerInverseSource m z)).re

/-- No imaginary part of the original physical Hamiltonian is discarded. -/
theorem birkhoffHillHierarchyHamiltonian_complex_value (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) :
    (D.birkhoffHillHierarchyHamiltonian m z : ℂ) = nativeHillHierarchyHamiltonian m (D.rawIntegerInverseSource m z) := by
  apply Complex.ext
  · rfl
  · exact (nativeHillHierarchyHamiltonian_im_eq_zero m _
      (D.rawIntegerInverseSource_real m z) (D.rawIntegerInverseSource_zero m z)).symm

/-- Every original hierarchy pullback is globally real analytic in the
original raw native source and target norms. -/
theorem birkhoffHillHierarchyHamiltonian_analytic (D : GlobalRoughAbelianForwardData) (m : ℕ) :
    AnalyticOnNhd ℝ (D.birkhoffHillHierarchyHamiltonian m) univ := by
  intro z _
  have hs := D.rawIntegerInverseSource_analytic m z (mem_univ _)
  have hH := (analyticAt_nativeHillHierarchyHamiltonian m (D.rawIntegerInverseSource m z)).restrictScalars (𝕜 := ℝ)
  exact (Complex.reCLM.analyticAt _).comp (hH.comp (f := D.rawIntegerInverseSource m) hs)

/-- The first printed KdV Hamiltonian is this SAME hierarchy member. -/
theorem birkhoffHillHierarchyHamiltonian_one (D : GlobalRoughAbelianForwardData)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((1 : ℕ) : ℝ)+1/2))) :
    D.birkhoffHillHierarchyHamiltonian 1 z = D.birkhoffKdVHamiltonian z := by
  unfold birkhoffHillHierarchyHamiltonian birkhoffKdVHamiltonian
  rw [nativeHillHierarchyHamiltonian_one]

/-- The printed KdV2 Hamiltonian is the second member with the SAME inverse. -/
theorem birkhoffHillHierarchyHamiltonian_two (D : GlobalRoughAbelianForwardData)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((2 : ℕ) : ℝ)+1/2))) :
    D.birkhoffHillHierarchyHamiltonian 2 z = D.birkhoffKdV2Hamiltonian z := by
  unfold birkhoffHillHierarchyHamiltonian birkhoffKdV2Hamiltonian
  rw [nativeHillHierarchyHamiltonian_two]

/-- Full signed matching recovers the original physical H_m at ANY given
real mean-zero H^m source, with no independent inverse choice. -/
theorem birkhoffHillHierarchyHamiltonian_eq_native_of_signed_eq
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (q : ScalarSobolev m)
    (hq : ∀ n : ℤ, q.val (-n) = conj (q.val n)) (hqm : q.val 0 = 0)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2)))
    (h : D.signed (nativeHillSource m q) = WeightedCoeff.sobolevInclusion
      (by have := Nat.cast_nonneg (α := ℝ) m; linarith : (-1/2 : ℝ) ≤ (m : ℝ)+1/2) z.val) :
    (D.birkhoffHillHierarchyHamiltonian m z : ℂ) = nativeHillHierarchyHamiltonian m q := by
  rw [D.birkhoffHillHierarchyHamiltonian_complex_value,
    D.rawIntegerInverseSource_eq_of_signed_eq m q hq hqm z h]

/-- The full hierarchy clause of Theorem 1.1(iii): EVERY original physical
H_m is an analytic function of the complete ORIGINAL actions alone, in the
exact weighted l1 action norm of order 2m+1. Every closed gap is included. -/
theorem exists_originalKdVHierarchy_real_analytic_action_factor
    (D : GlobalRoughAbelianForwardData) (m : ℕ) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev (2*(m : ℝ)+1)) 1),
      ∃ g : WeightedCoeff (Weight.sobolev (2*(m : ℝ)+1)) 1 → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*(m : ℝ)+1)) 1 ⊆ U ∧
      AnalyticOnNhd ℂ g U ∧
      (∀ z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2)),
        g (hierarchyNativeActionSequence m z) = (D.birkhoffHillHierarchyHamiltonian m z : ℂ)) ∧
      ∀ I : WeightedCoeff (Weight.sobolev (2*(m : ℝ)+1)) 1,
        I ∈ WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*(m : ℝ)+1)) 1 →
        (∀ n : ℤ, n ≤ 0 → I.val n = 0) → (g I).im = 0 := by
  obtain ⟨U,g,hU,hpos,hg,hrec⟩ := D.exists_rawNativeHamiltonian_analytic_action_factor m
    (2*(m : ℝ)+1) (by ring) (nativeHillHierarchyHamiltonian m)
    (fun q _ => analyticAt_nativeHillHierarchyHamiltonian m q)
    (nativeHillHierarchyHamiltonian_eq_of_discriminant_eq m)
  have hrecovery (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) :
      g (hierarchyNativeActionSequence m z) = (D.birkhoffHillHierarchyHamiltonian m z : ℂ) :=
    (hrec z).trans (D.birkhoffHillHierarchyHamiltonian_complex_value m z).symm
  refine ⟨U,g,hU,hpos,hg,hrecovery,?_⟩
  intro I hI hzero
  obtain ⟨z,hz⟩ := exists_sobolevSignedActionSequence_preimage (2*(m : ℝ)+1) ((m : ℝ)+1/2)
    (by ring) I hI hzero
  have he := hrecovery z
  change hierarchyNativeActionSequence m z = I at hz
  rw [hz] at he
  rw [he]
  exact Complex.ofReal_im _

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
