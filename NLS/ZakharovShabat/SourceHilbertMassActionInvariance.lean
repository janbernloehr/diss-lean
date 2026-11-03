import NLS.ZakharovShabat.SourceActionPhaseHilbertMass
import NLS.ZakharovShabat.SourceComponentSwap

/-! # The original Hilbert mass on action levels and component exchange -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.ZakharovShabat

/-- Equality of every original spectral action fixes the physical Hilbert mass. -/
theorem SourceBirkhoffMapComplexData.hilbertMass_eq_of_actions
    {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ ψ : realTypeSourceSubmodule 2)
    (h : ψ ∈ sourceRealActionLevelSet (by simp) (by norm_num) φ) :
    sourceHilbertMass ψ.val = sourceHilbertMass φ.val := by
  rw [← D.hilbert_complexTotalAction_eq_mass ψ,← D.hilbert_complexTotalAction_eq_mass φ,
    D.hilbert_complexTotalAction_eq_tsum _ (D.real_subset ψ.property),
    D.hilbert_complexTotalAction_eq_tsum _ (D.real_subset φ.property)]
  apply tsum_congr
  intro n
  rw [sourceComplexAction_eq_sourceRealAction _ _ _ _ ψ.property,
    sourceComplexAction_eq_sourceRealAction _ _ _ _ φ.property]
  apply Complex.ext
  · exact h n
  · rw [(sourceRealAction_nonneg_and_eq_zero_iff_gap_zero _ _ ψ.val ψ.property n).2.1,
      (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero _ _ φ.val φ.property n).2.1]

/-- Unsigned component exchange leaves the actual real Hilbert mass unchanged. -/
theorem sourceHilbertMass_componentSwap (φ : realTypeSourceSubmodule 2) :
    sourceHilbertMass (realSourceComponentSwap φ).val = sourceHilbertMass φ.val := by
  rw [sourceHilbertMass_eq_half_norm_sq_of_realType _ (realSourceComponentSwap φ).property,
    sourceHilbertMass_eq_half_norm_sq_of_realType _ φ.property]
  rw [realSourceComponentSwap_val,(sourceComponentSwap (p := 2)).norm_map]

end NLS.ZakharovShabat
