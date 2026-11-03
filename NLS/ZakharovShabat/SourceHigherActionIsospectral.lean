import NLS.ZakharovShabat.SourceLaurentActionIsospectral
import NLS.ZakharovShabat.SobolevOddHamiltonianTrace
import NLS.ZakharovShabat.SobolevNLSHierarchyTrace

/-! # Higher actions and sharp odd Hamiltonians are isospectral invariants

The real higher-action integrands depend only on the labelled endpoints
and normalized discriminant. The sharp trace then proves invariance of
H_(2s+1) on its full original real H^s domain, without smoothness premises.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceRealHigherAction_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) (k : ℕ) :
    sourceRealHigherAction hp hp1 ψ n k = sourceRealHigherAction hp hp1 φ n k := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  have hΔ := (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).mp h
  simp only [sourceRealHigherAction,canonicalPeriodicGap,sourceRealGapCosineProfile,
    sourceRealGapArcoshProfile,realGapAffinePoint,realGapHalfDiscriminant,hl,hr,hΔ]

theorem sourceComplexHigherAction_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) (k : ℕ) :
    sourceComplexHigherAction hp hp1 n k ψ.val = sourceComplexHigherAction hp hp1 n k φ.val := by
  rw [sourceComplexHigherAction_eq_real hp hp1 ψ n k,sourceComplexHigherAction_eq_real hp hp1 φ n k,
    sourceRealHigherAction_eq_of_isospectral hp hp1 φ ψ h n k]

theorem sourceComplexHigherAction_eq_of_actions (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceRealActionLevelSet hp hp1 φ) (n : ℤ) (k : ℕ) :
    sourceComplexHigherAction hp hp1 n k ψ.val = sourceComplexHigherAction hp hp1 n k φ.val := by
  apply sourceComplexHigherAction_eq_of_isospectral hp hp1 φ ψ _ n k
  rwa [sourceIsospectralSet_eq_actionLevelSet_all_exponents hp hp1 φ]

/-- Physical hierarchy conservation on every original admissible H^s
domain, including the H^0 mass endpoint. -/
theorem sobolevNLSHamiltonian_eq_of_isospectral (s n : ℕ) (hn : n ≤ s)
    (a b : realTypeHigherSobolevSourceLocus s)
    (h : (⟨higherSobolevSourceInclusion s b.val,b.property⟩ : realTypeSourceSubmodule 2) ∈
      sourceIsospectralSet (by simp) ⟨higherSobolevSourceInclusion s a.val,a.property⟩) :
    sobolevNLSHamiltonian s b.val (n+1) (by omega) = sobolevNLSHamiltonian s a.val (n+1) (by omega) := by
  have ht : sobolevNLSHamiltonian s b.val (n+1) (by omega)/2^n =
      sobolevNLSHamiltonian s a.val (n+1) (by omega)/2^n := by
    rw [← sobolevNLSHamiltonian_higherAction_trace s n hn b,
      ← sobolevNLSHamiltonian_higherAction_trace s n hn a]
    apply tsum_congr
    intro j
    exact sourceComplexHigherAction_eq_of_isospectral (by simp) (by norm_num)
      ⟨_,a.property⟩ ⟨_,b.property⟩ h j n
  exact (div_left_inj' (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))).mp ht

/-- The actual sharp odd physical Hamiltonian is constant on every
isospectral fiber in its full original Sobolev domain. -/
theorem sobolevOddHamiltonian_eq_of_isospectral (s : ℕ) (hs : 1 ≤ s)
    (a b : realTypeHigherSobolevSourceLocus s)
    (h : (⟨higherSobolevSourceInclusion s b.val,b.property⟩ : realTypeSourceSubmodule 2) ∈
      sourceIsospectralSet (by simp) ⟨higherSobolevSourceInclusion s a.val,a.property⟩) :
    sobolevOddHamiltonian s hs b.val = sobolevOddHamiltonian s hs a.val := by
  have ht : sobolevOddHamiltonian s hs b.val/4^s = sobolevOddHamiltonian s hs a.val/4^s := by
    rw [← sobolevOddHamiltonian_higherAction_trace s hs b,
      ← sobolevOddHamiltonian_higherAction_trace s hs a]
    apply tsum_congr
    intro n
    exact sourceComplexHigherAction_eq_of_isospectral (by simp) (by norm_num)
      ⟨_,a.property⟩ ⟨_,b.property⟩ h n (2*s)
  exact (div_left_inj' (pow_ne_zero s (by norm_num : (4 : ℂ) ≠ 0))).mp ht

end NLS.ZakharovShabat
