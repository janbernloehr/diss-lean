import NLS.ZakharovShabat.SourceActionPhaseFlow
import NLS.ZakharovShabat.SourceMassActionDifferential

/-! # Actual complex physical mass conservation for Hilbert phase lifts -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.ZakharovShabat.SourceActionFrequency
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Preservation of the original actions preserves the independently defined
complex physical Hilbert mass, including its original Fourier normalization. -/
theorem imageFlow_hilbertMass (F : SourceActionFrequency (p := 2) (by simp) (by norm_num))
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (time : ℝ) (ht : (time,φ) ∈ F.imageDomain D) :
    sourceHilbertMass (F.imageFlow D φ time).val = sourceHilbertMass φ.val := by
  rw [← D.hilbert_complexTotalAction_eq_mass (F.imageFlow D φ time),← D.hilbert_complexTotalAction_eq_mass φ,
    D.hilbert_complexTotalAction_eq_tsum _ (D.real_subset (F.imageFlow D φ time).property),
    D.hilbert_complexTotalAction_eq_tsum _ (D.real_subset φ.property)]
  exact tsum_congr (fun n => F.imageFlow_action D φ time ht n)

end NLS.ZakharovShabat.SourceActionFrequency
