import NLS.ZakharovShabat.SourceH1EndpointActionBound

/-! # The remaining spectral condition at the endpoint of Lemma 27.2

The kinetic slack and the cubic-moment sum are individually nonnegative.
The printed estimate is equivalent to their satisfying the lower bound below.
No global quantitative lower bound for the cubic moments is assumed.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The amount lost when bounding kinetic actions plus mass by the weighted action sum. -/
def sourceH1KineticActionSlack (a : realTypeSobolevSourceLocus) : ℝ :=
  (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)-
  (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)-
  (∑' n : ℤ, (sourceSobolevWeightedAction a.val n).re)

theorem sourceH1KineticActionSlack_nonneg (a : realTypeSobolevSourceLocus) :
    0 ≤ sourceH1KineticActionSlack a := by
  unfold sourceH1KineticActionSlack
  rw [sourceH1_sum_actions_eq_mass]
  linarith [sourceH1_kinetic_actions_add_mass_le a]

namespace SourcePrimitivePowerAtlas
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
variable {W : Set (CoeffPair 4)}
variable (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)

/-- The energy budget with both discarded nonnegative quantities restored exactly. -/
theorem sourceH1_energy_eq_mass_budget_sub_moments (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevHamiltonian a.val).re =
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)-
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)+
      2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)^2-
      sourceH1KineticActionSlack a-
      (4/3:ℝ)*(∑' n : ℤ, (A.moment n 3 (sobolevSourceFL4 a.val)).re) := by
  have h := congrArg Complex.re (A.renormalizedHamiltonian_eq_sobolevPhysicalCorrection a)
  have he := A.real_renormalizedHamiltonian_eq_real_tsum
    (⟨sobolevSourceFL4 a.val,(realSobolevSourceFL4 a).property⟩ : realTypeSourceSubmodule 4)
  rw [he,Complex.ofReal_re,sourceSobolevPhysicalCorrection,
    sourceSobolevWeightedActionSum_eq_tsum _ a.property] at h
  have hs := (summable_norm_sourceSobolevWeightedAction a.val a.property).of_norm
  have hm : (2*(periodOneSobolevMass a.val)^2).re =
      2*(periodOneSobolevMass a.val).re^2 := by
    rw [periodOneSobolevMass_real_eq]
    norm_cast
  rw [Complex.sub_re,Complex.sub_re,hm,Complex.re_tsum hs] at h
  unfold sourceH1KineticActionSlack
  rw [sourceH1_sum_actions_eq_mass]
  linarith

/-- Exact reduction of the literal endpoint to a quantitative cubic-moment estimate. -/
theorem sourceH1_lemma272_iff_moment_budget (a : realTypeSobolevSourceLocus) :
    ((periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      (1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)) ↔
    2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)^2-
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)-
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)-
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)^2 ≤
      sourceH1KineticActionSlack a+
        (4/3:ℝ)*(∑' n : ℤ, (A.moment n 3 (sobolevSourceFL4 a.val)).re) := by
  rw [A.sourceH1_energy_eq_mass_budget_sub_moments a]
  constructor <;> intro h <;> nlinarith

end SourcePrimitivePowerAtlas
end NLS.ZakharovShabat
