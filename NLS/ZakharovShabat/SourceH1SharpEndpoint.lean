import NLS.ZakharovShabat.SourcePrimitivePowerGlobalCubic
import NLS.ZakharovShabat.SourceH1ZeroModeMomentCriterion

/-! # The unrestricted H1 endpoint in Lemma 27.2

The sharp zero-mode cubic bound proves H3 <= 2*S+S^2 and the stronger
H3 <= S-M+S^2 with the original physical energy and action weights.
No profile representation or smallness hypothesis remains.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The literal unrestricted m=1 endpoint in Lemma 27.2. -/
theorem sourceH1_energy_le_lemma272 (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      (1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) := by
  let φ : realTypeSourceSubmodule 4 := ⟨sobolevSourceFL4 a.val,(realSobolevSourceFL4 a).property⟩
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (by simp : (4:ℝ≥0∞) ≠ ⊤) (by norm_num)
  have h := A.real_action_sq_le_cubic φ 0
  rw [← sourceH1_actionTerm_zero_eq_FL4 a 0] at h
  exact A.sourceH1_energy_le_lemma272_of_zero_moment a h

/-- The sharp zero-mode moment gives a stronger global H1 budget. -/
theorem sourceH1_energy_le_quadratic_budget (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)-
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)+
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)^2 := by
  let φ : realTypeSourceSubmodule 4 := ⟨sobolevSourceFL4 a.val,(realSobolevSourceFL4 a).property⟩
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (by simp : (4:ℝ≥0∞) ≠ ⊤) (by norm_num)
  have h := A.real_action_sq_le_cubic φ 0
  rw [← sourceH1_actionTerm_zero_eq_FL4 a 0] at h
  exact A.sourceH1_energy_le_quadratic_budget_of_zero_moment a h

end NLS.ZakharovShabat
