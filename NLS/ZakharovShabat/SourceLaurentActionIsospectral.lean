import NLS.ZakharovShabat.SourceDiagonalLaurentAtlas
import NLS.ZakharovShabat.SourceActionIsospectralAllExponents

/-! # Isospectral invariance of every integer Laurent level

The real formula uses only the canonically labelled endpoints and the
normalized discriminant. Equality of the original NLS actions therefore
preserves every Laurent level on its actual source domain.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- No restriction on the integer level or gap size is needed for the
real formula: equal spectral data give literally the same integrand. -/
theorem sourceRealLaurentAction_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n k : ℤ) :
    sourceRealLaurentAction hp hp1 ψ n k = sourceRealLaurentAction hp hp1 φ n k := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  have hΔ := (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).mp h
  simp only [sourceRealLaurentAction,canonicalPeriodicGap,sourceRealGapCosineProfile,
    sourceRealGapArcoshProfile,realGapAffinePoint,realGapHalfDiscriminant,hl,hr,hΔ]

/-- Equal original actions determine the actual real Laurent actions. -/
theorem sourceRealLaurentAction_eq_of_actions (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceRealActionLevelSet hp hp1 φ) (n k : ℤ) :
    sourceRealLaurentAction hp hp1 ψ n k = sourceRealLaurentAction hp hp1 φ n k := by
  apply sourceRealLaurentAction_eq_of_isospectral hp hp1 φ ψ _ n k
  rwa [sourceIsospectralSet_eq_actionLevelSet_all_exponents hp hp1 φ]

/-- Invariance is asserted only where the actual analytic contour
extension is defined. This includes all real diagonals. -/
theorem sourceDiagonalLaurentAction_real_eq_of_actions (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ sourceDiagonalLaurentDomain hp hp1)
    (hψ : ψ.val ∈ sourceDiagonalLaurentDomain hp hp1)
    (h : ψ ∈ sourceRealActionLevelSet hp hp1 φ) (n k : ℤ) (hn : n ≠ 0) :
    sourceDiagonalLaurentAction hp hp1 n k ψ.val = sourceDiagonalLaurentAction hp hp1 n k φ.val := by
  rw [sourceDiagonalLaurentAction_eq_real hp hp1 ψ hψ n k hn,
    sourceDiagonalLaurentAction_eq_real hp hp1 φ hφ n k hn]
  exact sourceRealLaurentAction_eq_of_actions hp hp1 φ ψ h n k

end NLS.ZakharovShabat
