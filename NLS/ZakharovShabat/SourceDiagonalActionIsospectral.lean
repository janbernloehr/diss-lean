import NLS.ZakharovShabat.SourceDiagonalActionRoot
import NLS.ZakharovShabat.SourceLaurentActionIsospectral

/-! # Isospectral invariance of the actual diagonal action scaling

The normalized quotient is spectral at an open gap. At a closed gap its
proved value is the reciprocal of twice the actual spectral midpoint.
Thus both the regularized ratio and its chosen square root are invariant
on every actual real diagonal isospectral set, including all closed gaps.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceDiagonalLaurentAction_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realDiagonalSourceLocus p)
    (h : (⟨ψ.val,ψ.property.1⟩ : realTypeSourceSubmodule p) ∈
      sourceIsospectralSet hp ⟨φ.val,φ.property.1⟩) (n k : ℤ) (hn : n ≠ 0) :
    sourceDiagonalLaurentAction hp hp1 n k ψ.val = sourceDiagonalLaurentAction hp hp1 n k φ.val := by
  rw [sourceDiagonalLaurentAction_eq_real hp hp1 ⟨ψ.val,ψ.property.1⟩
      (realDiagonal_subset_sourceDiagonalLaurentDomain hp hp1 ψ.property) n k hn,
    sourceDiagonalLaurentAction_eq_real hp hp1 ⟨φ.val,φ.property.1⟩
      (realDiagonal_subset_sourceDiagonalLaurentDomain hp hp1 φ.property) n k hn]
  exact sourceRealLaurentAction_eq_of_isospectral hp hp1 _ _ h n k

/-- The physical inverse-frequency ratio is invariant even when the
selected action is zero. No division by that action is used there. -/
theorem sourceDiagonalActionRatio_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realDiagonalSourceLocus p)
    (h : (⟨ψ.val,ψ.property.1⟩ : realTypeSourceSubmodule p) ∈
      sourceIsospectralSet hp ⟨φ.val,φ.property.1⟩) (n : ℤ) (hn : n ≠ 0) :
    sourceDiagonalActionRatio hp hp1 n ψ.val = sourceDiagonalActionRatio hp hp1 n φ.val := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  have hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem _) n =
      canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n := by
    simp only [canonicalPeriodicGap,hl,hr]
  by_cases hz : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n = 0
  · rw [sourceDiagonalActionRatio_zeroGap hp hp1 ψ n (hg.trans hz),
      sourceDiagonalActionRatio_zeroGap hp hp1 φ n hz]
    simp only [sourceStandardRootMidpoint,canonicalPeriodicMidpoint,hl,hr]
  · obtain ⟨U,_,hψU,_,hLψ⟩ := exists_local_sourceNormalizedDiagonalLaurentAction_analytic_factor hp hp1 ψ n hn
    obtain ⟨V,_,hφV,_,hLφ⟩ := exists_local_sourceNormalizedDiagonalLaurentAction_analytic_factor hp hp1 φ n hn
    have hL := sourceDiagonalLaurentAction_eq_of_isospectral hp hp1 φ ψ h n 0 hn
    rw [hLψ ψ.val hψU,hLφ φ.val hφV,hg] at hL
    have hNL := mul_left_cancel₀ (pow_ne_zero 2 hz) hL
    obtain ⟨A,_,hψA,_,hIψ⟩ := exists_local_sourceNormalizedAction_analytic_factor hp hp1 ψ.val ψ.property.1 n
    obtain ⟨B,_,hφB,_,hIφ⟩ := exists_local_sourceNormalizedAction_analytic_factor hp hp1 φ.val φ.property.1 n
    have hI : sourceComplexAction hp hp1 n ψ.val = sourceComplexAction hp hp1 n φ.val := by
      rw [sourceComplexAction_eq_sourceRealAction hp hp1 n ψ.val ψ.property.1,
        sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property.1]
      exact sourceRealAction_eq_of_isospectral hp hp1 _ _ h n
    rw [hIψ ψ.val hψA,hIφ φ.val hφB,sourcePeriodicGapDisplacement_apply,sourcePeriodicGapDisplacement_apply,hg] at hI
    have hNI := mul_left_cancel₀ (pow_ne_zero 2 hz) hI
    exact congrArg₂ (fun a b : ℂ => a/(2*b)) hNL hNI

theorem sourceDiagonalActionRoot_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realDiagonalSourceLocus p)
    (h : (⟨ψ.val,ψ.property.1⟩ : realTypeSourceSubmodule p) ∈
      sourceIsospectralSet hp ⟨φ.val,φ.property.1⟩) (n : ℤ) (hn : n ≠ 0) :
    sourceDiagonalActionRoot hp hp1 n ψ.val = sourceDiagonalActionRoot hp hp1 n φ.val :=
  congrArg Complex.sqrt (sourceDiagonalActionRatio_eq_of_isospectral hp hp1 φ ψ h n hn)

end NLS.ZakharovShabat
