import NLS.ZakharovShabat.SourceFiniteGap
import NLS.ZakharovShabat.SourcePsiGapRootIsospectral

/-! Actual full signed Dirac isospectrality preserves genuine finite-gap
membership, including the central gap and every original label. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceFiniteGap_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (h : ψ ∈ sourceIsospectralSet hp φ) : ψ ∈ sourceFiniteGapLocus hp hp1 := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val) (periodOnePotential_mem _) (periodOnePotential_mem _)
    h.1 h.2
  change {k : ℤ | canonicalPeriodicRight hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem _) k-
    canonicalPeriodicLeft hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem _) k ≠ 0}.Finite
  rw [hl,hr]
  exact hf

end NLS.ZakharovShabat
