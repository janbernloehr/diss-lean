import NLS.ZakharovShabat.SourceOriginalSpectralConservation
import NLS.ZakharovShabat.SourceActionRegularPoisson
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # Independent original action integrals in involution

This implements the original dynamics statements in the introduction, printed p. 9.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original real spectral action as a function of the original real source. -/
def originalRealActionIntegral (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) : ℝ := (sourceComplexAction hp hp1 n φ.val).re

/-- A one-mode original source separates any selected action from every other one. -/
theorem exists_originalRealActionIntegral_single (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hp2 : p ≤ 2) (n : ℤ) :
    ∃ φ : realTypeSourceSubmodule p, ∀ k : ℤ,
      originalRealActionIntegral hp hp1 k φ = if k = n then 1/2 else 0 := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection17_original hp hp1
  obtain ⟨φ,hφ⟩ := D.proposition17_3 hp2 ((lp.single p n 1 : RealCoeff p),0)
  refine ⟨φ,?_⟩
  intro k
  rw [originalRealActionIntegral,sourceComplexAction_eq_sourceRealAction hp hp1 k _ φ.property,
    ← D.complex.real_pairAction_eq φ k,hφ]
  by_cases hk : k = n <;> simp [RealCoeff.pairAction,lp.single_apply,hk]

/-- The infinitely many original action functions are linearly independent. -/
theorem linearIndependent_originalRealActionIntegral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hp2 : p ≤ 2) : LinearIndependent ℝ (originalRealActionIntegral hp hp1) := by
  classical
  rw [linearIndependent_iff']
  intro S a ha n hn
  obtain ⟨φ,hφ⟩ := exists_originalRealActionIntegral_single hp hp1 hp2 n
  have he := congrFun ha φ
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,hφ] at he
  have hz : a n * (1/2:ℝ) = 0 := by simpa [hn] using he
  linarith

/-- Each member of the independent action family is conserved by every original global ordinary solution. -/
theorem originalRealActionIntegral_of_isOrdinaryNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsOrdinaryNLSSolutionOn univ φ γ) (τ : ℝ) (n : ℤ) :
    originalRealActionIntegral hp hp1 n (γ τ) = originalRealActionIntegral hp hp1 n φ :=
  congrArg Complex.re (sourceComplexAction_of_isOrdinaryNLSSolutionOn_univ hp hp1 hp2 hγ τ n)

/-- The same independent integrals are conserved by every original global renormalized solution. -/
theorem originalRealActionIntegral_of_isRenormalizedNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsRenormalizedNLSSolutionOn univ φ γ) (τ : ℝ) (n : ℤ) :
    originalRealActionIntegral hp hp1 n (γ τ) = originalRealActionIntegral hp hp1 n φ :=
  congrArg Complex.re (sourceComplexAction_of_isRenormalizedNLSSolutionOn_univ hp hp1 hp2 hγ τ n)

/-- Infinitely many independent original first integrals commute under the physical Poisson pairing. -/
theorem originalOrdinary_integrals_in_involution
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsOrdinaryNLSSolutionOn univ φ γ) :
    LinearIndependent ℝ (originalRealActionIntegral hp hp1) ∧
      (∀ τ n, originalRealActionIntegral hp hp1 n (γ τ) = originalRealActionIntegral hp hp1 n φ) ∧
      ∀ τ n m, (sourceActionRegularCotangent hp hp1 n ⟨(γ τ).val,(γ τ).property⟩).bivector
        (sourceActionRegularCotangent hp hp1 m ⟨(γ τ).val,(γ τ).property⟩) = 0 :=
  ⟨linearIndependent_originalRealActionIntegral hp hp1 hp2,
    originalRealActionIntegral_of_isOrdinaryNLSSolutionOn_univ hp hp1 hp2 hγ,
    fun τ n m => sourceActionRegularCotangent_bivector_eq_zero hp hp1 n m ⟨(γ τ).val,(γ τ).property⟩⟩

/-- The renormalized physical flow retains the same independent integrals in involution. -/
theorem originalRenormalized_integrals_in_involution
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsRenormalizedNLSSolutionOn univ φ γ) :
    LinearIndependent ℝ (originalRealActionIntegral hp hp1) ∧
      (∀ τ n, originalRealActionIntegral hp hp1 n (γ τ) = originalRealActionIntegral hp hp1 n φ) ∧
      ∀ τ n m, (sourceActionRegularCotangent hp hp1 n ⟨(γ τ).val,(γ τ).property⟩).bivector
        (sourceActionRegularCotangent hp hp1 m ⟨(γ τ).val,(γ τ).property⟩) = 0 :=
  ⟨linearIndependent_originalRealActionIntegral hp hp1 hp2,
    originalRealActionIntegral_of_isRenormalizedNLSSolutionOn_univ hp hp1 hp2 hγ,
    fun τ n m => sourceActionRegularCotangent_bivector_eq_zero hp hp1 n m ⟨(γ τ).val,(γ τ).property⟩⟩

end NLS.ZakharovShabat
