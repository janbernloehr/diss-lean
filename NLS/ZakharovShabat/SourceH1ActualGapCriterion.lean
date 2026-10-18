import NLS.ZakharovShabat.SourceExteriorGapCorrection
import NLS.ZakharovShabat.SourceH1ZeroModeMomentCriterion

/-! # The H1 endpoint from one explicit spectral profile identity

The actual H1 action trace supplies the integrable kernel majorant, and
the moment atlas is constructed internally. The sole remaining premise
is equality of the actual zero-gap profile with the specified candidate.
This file does not prove that identity or the unrestricted endpoint.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The literal H1 endpoint is reduced to one identity for an explicit, integrable spectral candidate. -/
theorem sourceH1_energy_le_lemma272_of_actual_zero_gap_identity (a : realTypeSobolevSourceLocus)
    (hrep : let φ : realTypeSourceSubmodule 4 := ⟨sobolevSourceFL4 a.val,(realSobolevSourceFL4 a).property⟩
      ∀ x ∈ Icc (0:ℝ) Real.pi,
        sourceRealGapCosineProfile (by simp) (by norm_num) φ.val 0 x =
          sourceGapHalfWidthReal (by simp) (by norm_num) φ 0*Real.sin x*
            (1+sourceExteriorGapCorrection (by simp) (by norm_num) φ 0 x)) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      (1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) := by
  let φ : realTypeSourceSubmodule 4 := ⟨sobolevSourceFL4 a.val,(realSobolevSourceFL4 a).property⟩
  have ha : Summable (fun m : ℤ => ‖sourceComplexAction (by simp) (by norm_num) m φ.val‖) :=
    (sourceWeightedActionTerm_zero_summable (sourceH1RealSource a)).congr (sourceH1_actionTerm_zero_eq_FL4 a)
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (by simp : (4:ℝ≥0∞) ≠ ⊤) (by norm_num)
  have h := A.real_action_sq_le_cubic_of_actual_gap_identity φ 0 ha hrep
  rw [← sourceH1_actionTerm_zero_eq_FL4 a 0] at h
  exact A.sourceH1_energy_le_lemma272_of_zero_moment a h

end NLS.ZakharovShabat
