import NLS.ZakharovShabat.SourceH1ZeroModeActionBound
import NLS.ZakharovShabat.SourceH1EndpointMomentCriterion

/-! # A zero-gap cubic moment criterion for Lemma 27.2

The exact H1 energy identity and nonnegativity of all cubic moments reduce
the unrestricted endpoint to the single bound R_0 >= (3/4)*I_0^2.
The criterion keeps this lower bound as an explicit hypothesis.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
namespace SourcePrimitivePowerAtlas
variable {W : Set (CoeffPair 4)} (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)

/-- A sharp cubic lower bound at the zero gap alone gives the stronger H1 budget. -/
theorem sourceH1_energy_le_quadratic_budget_of_zero_moment (a : realTypeSobolevSourceLocus)
    (hzero : (3/4:ℝ)*(sourceWeightedActionTerm (sourceH1RealSource a) 0 0)^2 ≤
      (A.moment 0 3 (sobolevSourceFL4 a.val)).re) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)-
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)+
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)^2 := by
  let I := sourceWeightedActionTerm (sourceH1RealSource a) 0
  let φ : realTypeSourceSubmodule 4 := ⟨sobolevSourceFL4 a.val,(realSobolevSourceFL4 a).property⟩
  have hI : ∀ n, 0 ≤ I n := by intro n;unfold I sourceWeightedActionTerm;positivity
  have hR : (A.moment 0 3 φ.val).re ≤ ∑' n : ℤ, (A.moment n 3 φ.val).re :=
    (A.summable_real_cubic_moments φ).le_tsum 0 (fun n _ => (A.real_moment_nonneg φ n 3).1)
  apply energy_bound_of_zero_mode_correction _ _ _ (I 0)
    ((4/3:ℝ)*(∑' n : ℤ, (A.moment n 3 φ.val).re))
  · exact tsum_nonneg hI
  · exact (sourceWeightedActionTerm_zero_summable (sourceH1RealSource a)).le_tsum 0 (fun n _ => hI n)
  · exact sourceH1_two_mass_sub_zero_action_le_weighted a
  · change (3/4:ℝ)*(I 0)^2 ≤ (A.moment 0 3 φ.val).re at hzero
    linarith
  · rw [A.sourceH1_energy_eq_mass_budget_sub_moments a]
    linarith [sourceH1KineticActionSlack_nonneg a]

/-- The zero-gap condition implies the literal unrestricted m=1 inequality. -/
theorem sourceH1_energy_le_lemma272_of_zero_moment (a : realTypeSobolevSourceLocus)
    (hzero : (3/4:ℝ)*(sourceWeightedActionTerm (sourceH1RealSource a) 0 0)^2 ≤
      (A.moment 0 3 (sobolevSourceFL4 a.val)).re) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      (1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) := by
  have h := A.sourceH1_energy_le_quadratic_budget_of_zero_moment a hzero
  have hm : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n := by
    apply tsum_nonneg;intro n;unfold sourceWeightedActionTerm;positivity
  have hs : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n := by
    apply tsum_nonneg;intro n;unfold sourceWeightedActionTerm;positivity
  nlinarith

end SourcePrimitivePowerAtlas
end NLS.ZakharovShabat
