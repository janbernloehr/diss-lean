import NLS.KdV.MiuraHillPsiNumerators
import NLS.ZakharovShabat.SourceAngularOriginalBetaSelectedBound

/-! The actual Hill family can be chosen WITH the retained original
all-index estimates. Its normalized numerator and periods remain the
same proved objects; no external regular-factor bound is assumed. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_miuraHillPsiFamily_with_original_estimates :
    ∃ A : MiuraHillPsiFamily,
      SourceLemma12_12Data (by norm_num) (by norm_num) A.originalDomain A.domain A.roots := by
  obtain ⟨W₀,hW₀,hC₀,hR₀,W,hW,hC,hR,s,H⟩ := sourceLemma12_12 (p := 2) (by norm_num) (by norm_num)
  exact ⟨⟨W₀,hW₀,hC₀,hR₀,W,hW,hC,hR,s,H.previous.previous.psi⟩,H⟩

end NLS.KdV
