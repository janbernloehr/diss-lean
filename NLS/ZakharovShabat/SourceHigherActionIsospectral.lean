import NLS.ZakharovShabat.SourceIsospectralSet
import NLS.ZakharovShabat.SourceRealHigherActionIntegral

/-! # Isospectral invariance of every original higher action

The literal gap integral uses only the normalized discriminant and its
canonically indexed endpoints. This includes every signed gap, collapsed
gaps, and every nonnegative moment order.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real arcosh profile agrees on the entire real axis under isospectrality. -/
theorem sourceRealGapArcoshProfile_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n : ℤ) (x : ℝ) :
    sourceRealGapArcoshProfile hp ψ.val n x =
      sourceRealGapArcoshProfile hp φ.val n x := by
  have hΔ := (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).mp h
  simp only [sourceRealGapArcoshProfile,realGapHalfDiscriminant,hΔ]

/-- Every original real higher action is a spectral invariant on its full domain. -/
theorem sourceRealHigherAction_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n : ℤ) (k : ℕ) :
    sourceRealHigherAction hp hp1 ψ n k = sourceRealHigherAction hp hp1 φ n k := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  simp only [sourceRealHigherAction_eq_gapIntegral,hl,hr,
    sourceRealGapArcoshProfile_eq_of_isospectral hp hp1 φ ψ h]

/-- The original contour-defined higher actions retain the same invariance. -/
theorem sourceIndexedHigherAction_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n : ℤ) (k : ℕ) :
    sourceIndexedHigherAction hp hp1 n k ψ.val =
      sourceIndexedHigherAction hp hp1 n k φ.val := by
  simp only [sourceIndexedHigherAction_eq_gapIntegral]
  have he := sourceRealHigherAction_eq_of_isospectral hp hp1 φ ψ h n k
  simpa only [sourceRealHigherAction_eq_gapIntegral] using congrArg (fun x : ℝ => (x : ℂ)) he

end NLS.ZakharovShabat
