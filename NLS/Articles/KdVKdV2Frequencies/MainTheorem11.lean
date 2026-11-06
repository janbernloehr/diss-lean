import NLS.Articles.KdVKdV2Frequencies.OriginalNativeBirkhoffIdentifications

/-! # Theorem 1.1: the original global Birkhoff map for the KdV hierarchy

This existential bundle keeps ONE complex mean-zero map and ONE neighborhood
throughout all four clauses. Every native real diffeomorphism is its literal
restriction, and the physical Hamiltonians are composed with those same
inverses. The original weights are (1+|n|)^s and the Fourier normalization is
(2|n|pi)^(-1/2). No abstract integrability or coordinate hypothesis is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies

/-- The full precise content of source Theorem 1.1, including the full
hierarchy strengthening. All spaces carry the original raw weighted norms. -/
structure OriginalBirkhoffTheoremData where
  domain : Set OriginalComplexBirkhoffSource
  map : OriginalComplexBirkhoffSource → OriginalComplexBirkhoffTarget
  domain_open : IsOpen domain
  real_mem_domain : ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (-1)),
    physicalRealToComplexMeanZeroWeighted _ q ∈ domain
  analytic : AnalyticOnNhd ℂ map domain
  map_zero : map 0 = 0
  native : ∀ (s : ℝ), -1 ≤ s →
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) ≃ₜ
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (s+1/2))
  native_analytic : ∀ s hs, AnalyticOnNhd ℝ (fun q => native s hs q) univ
  native_inverse_analytic : ∀ s hs, AnalyticOnNhd ℝ (native s hs).symm univ
  native_mem_domain : ∀ (s : ℝ) (hs : -1 ≤ s)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)), physicalRealMeanZeroSobolevToComplex hs q ∈ domain
  native_restriction : ∀ s hs q, map (physicalRealMeanZeroSobolevToComplex hs q) =
    physicalRealMeanZeroSobolevToComplex (by linarith : (-1/2 : ℝ) ≤ s+1/2) (native s hs q)
  canonical : ∀ q ∈ domain, ∀ (σ τ : Bool) (n m : ℕ+),
    NLS.Poisson.meanZeroHminusGardnerBracket
      (originalMeanZeroBirkhoffComponent map σ n)
      (originalMeanZeroBirkhoffComponent map τ m) q =
        hillOriginalComplexGardnerMatrixEntry σ τ n m/2
  hierarchy_pullback_analytic : ∀ m : ℕ,
    AnalyticOnNhd ℝ (fun z => (nativeHillHierarchyHamiltonian m
      ((native (m : ℝ) (by have := Nat.cast_nonneg (α := ℝ) m; linarith)).symm z).val).re) univ
  hierarchy_action_factor : ∀ m : ℕ,
    ∃ U : Set (WeightedCoeff (Weight.sobolev (2*(m : ℝ)+1)) 1),
      ∃ g : WeightedCoeff (Weight.sobolev (2*(m : ℝ)+1)) 1 → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*(m : ℝ)+1)) 1 ⊆ U ∧
      AnalyticOnNhd ℂ g U ∧
      (∀ z, g (hierarchyNativeActionSequence m z) = nativeHillHierarchyHamiltonian m
        ((native (m : ℝ) (by have := Nat.cast_nonneg (α := ℝ) m; linarith)).symm z).val) ∧
      ∀ I : WeightedCoeff (Weight.sobolev (2*(m : ℝ)+1)) 1,
        I ∈ WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*(m : ℝ)+1)) 1 →
        (∀ n : ℤ, n ≤ 0 → I.val n = 0) → (g I).im = 0
  fourier_differential : ∀ (h : OriginalComplexBirkhoffSource) (j : ℤ),
    (((fderiv ℂ map 0) h).val).val j =
      (Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val.val j
  native_fourier_differential : ∀ s hs
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) (j : ℤ),
    (((fderiv ℝ (fun q => native s hs q) 0) h).val).val j =
      (Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val.val j

/-- Source Theorem 1.1, proved without an assumed Birkhoff map or integrability
hypothesis. One existing actual physical rough map supplies every clause. -/
theorem theorem_1_1 : Nonempty OriginalBirkhoffTheoremData := by
  classical
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  let e := fun s hs => Classical.choose (D.exists_originalMeanZeroMap_native_diffeomorphism s hs)
  have he (s : ℝ) (hs : -1 ≤ s) := Classical.choose_spec
    (D.exists_originalMeanZeroMap_native_diffeomorphism s hs)
  have hinv (m : ℕ) (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) :
      D.rawIntegerInverseSource m z =
        ((e (m : ℝ) (by have := Nat.cast_nonneg (α := ℝ) m; linarith)).symm z).val :=
    D.originalMeanZeroMap_native_inverse_eq m _ (he _ _).2.2.1 (he _ _).2.2.2 z
  refine ⟨{
    domain := D.originalMeanZeroDomain
    map := D.originalMeanZeroMap
    domain_open := D.originalMeanZeroDomain_open
    real_mem_domain := D.real_mem_originalMeanZeroDomain
    analytic := D.originalMeanZeroMap_analytic
    map_zero := D.originalMeanZeroMap_zero
    native := e
    native_analytic := fun s hs => (he s hs).1
    native_inverse_analytic := fun s hs => (he s hs).2.1
    native_mem_domain := fun s hs => (he s hs).2.2.1
    native_restriction := fun s hs => (he s hs).2.2.2
    canonical := D.originalMeanZeroMap_gardner_matrix
    hierarchy_pullback_analytic := ?_
    hierarchy_action_factor := fun m => D.exists_originalMeanZeroMap_native_hierarchy_action_factor
      m _ (he _ _).2.2.1 (he _ _).2.2.2
    fourier_differential := D.originalMeanZeroMap_fourier_differential
    native_fourier_differential := fun s hs => D.originalMeanZeroMap_native_fourier_differential
      s hs _ (he s hs).1 (he s hs).2.2.2
  }⟩
  intro m
  have heq : (fun z => (nativeHillHierarchyHamiltonian m
      ((e (m : ℝ) (by have := Nat.cast_nonneg (α := ℝ) m; linarith)).symm z).val).re) =
      D.birkhoffHillHierarchyHamiltonian m := by
    funext z
    unfold GlobalRoughAbelianForwardData.birkhoffHillHierarchyHamiltonian
    rw [hinv m z]
  rw [heq]
  exact D.birkhoffHillHierarchyHamiltonian_analytic m

namespace OriginalBirkhoffTheoremData

/-- The exact printed mixed bracket, in the intrinsic mean-zero source. -/
theorem gardner_positive_negative (T : OriginalBirkhoffTheoremData)
    (q : OriginalComplexBirkhoffSource) (hq : q ∈ T.domain) (n m : ℕ+) :
    NLS.Poisson.meanZeroHminusGardnerBracket
      (originalMeanZeroBirkhoffComponent T.map true n)
      (originalMeanZeroBirkhoffComponent T.map false m) q = if n = m then I else 0 := by
  rw [T.canonical q hq]
  by_cases h : n = m
  · subst m
    simp [hillOriginalComplexGardnerMatrixEntry]
  · have hnm : (n : ℕ) ≠ (m : ℕ) := fun he => h (Subtype.ext he)
    simp [hillOriginalComplexGardnerMatrixEntry,hnm,h]

/-- All brackets of coordinates with the same sign vanish. -/
theorem gardner_same_sign (T : OriginalBirkhoffTheoremData)
    (q : OriginalComplexBirkhoffSource) (hq : q ∈ T.domain) (σ : Bool) (n m : ℕ+) :
    NLS.Poisson.meanZeroHminusGardnerBracket
      (originalMeanZeroBirkhoffComponent T.map σ n)
      (originalMeanZeroBirkhoffComponent T.map σ m) q = 0 := by
  rw [T.canonical q hq]
  cases σ <;> simp [hillOriginalComplexGardnerMatrixEntry]

/-- The physical printed KdV Hamiltonian composed with this same inverse. -/
theorem kdv_action_factor (T : OriginalBirkhoffTheoremData) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev (2*((1 : ℕ) : ℝ)+1)) 1),
      ∃ g : WeightedCoeff (Weight.sobolev (2*((1 : ℕ) : ℝ)+1)) 1 → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*((1 : ℕ) : ℝ)+1)) 1 ⊆ U ∧
      AnalyticOnNhd ℂ g U ∧
      (∀ z, g (hierarchyNativeActionSequence 1 z) = nativeKdVHamiltonian
        ((T.native ((1 : ℕ) : ℝ) (by norm_num)).symm z).val) ∧
      ∀ I : WeightedCoeff (Weight.sobolev (2*((1 : ℕ) : ℝ)+1)) 1,
        I ∈ WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*((1 : ℕ) : ℝ)+1)) 1 →
        (∀ n : ℤ, n ≤ 0 → I.val n = 0) → (g I).im = 0 := by
  simpa only [nativeHillHierarchyHamiltonian_one] using T.hierarchy_action_factor 1

/-- The physical printed KdV2 Hamiltonian composed with this same inverse. -/
theorem kdv2_action_factor (T : OriginalBirkhoffTheoremData) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev (2*((2 : ℕ) : ℝ)+1)) 1),
      ∃ g : WeightedCoeff (Weight.sobolev (2*((2 : ℕ) : ℝ)+1)) 1 → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*((2 : ℕ) : ℝ)+1)) 1 ⊆ U ∧
      AnalyticOnNhd ℂ g U ∧
      (∀ z, g (hierarchyNativeActionSequence 2 z) = nativeKdV2Hamiltonian
        ((T.native ((2 : ℕ) : ℝ) (by norm_num)).symm z).val) ∧
      ∀ I : WeightedCoeff (Weight.sobolev (2*((2 : ℕ) : ℝ)+1)) 1,
        I ∈ WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*((2 : ℕ) : ℝ)+1)) 1 →
        (∀ n : ℤ, n ≤ 0 → I.val n = 0) → (g I).im = 0 := by
  simpa only [nativeHillHierarchyHamiltonian_two] using T.hierarchy_action_factor 2

end OriginalBirkhoffTheoremData
end NLS.Articles.KdVKdV2Frequencies
