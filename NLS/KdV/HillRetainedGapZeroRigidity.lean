import NLS.KdV.HillEnergyGapZeroUniqueness
import NLS.ComplexAnalysis.QuadraticRootReplacementGrowth
import NLS.ZakharovShabat.CentralCircleThresholds

/-! Sub-sine growth and one zero in each retained original gap force
an EXACT zero set and simple zeros for every nonzero entire Hill energy
numerator. Removing an extra or multiple zero and inserting a zero in
the omitted gap would contradict the proved all-gap interpolation theorem.
No product representation or normalization constant is assumed. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

variable (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
  (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
  (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q))
  (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) (hnz : P ≠ 0) (n : ℕ+) (σ : ℕ+ → ℝ)
  (hσ : ∀ m : ℕ+, σ m ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))))
  (hzero : ∀ m : ℕ+, m ≠ n → P (σ m:ℂ) = 0)
  (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k), ‖(2*z*P (z^2-(c:ℂ)))/(-2*sin z)‖ ≤ ε)

include hi hc hP hnz hσ hzero hsmall

theorem hillMiura_energy_zero_iff_retained_sample (a : ℂ) :
    P a = 0 ↔ ∃ m : ℕ+, m ≠ n ∧ (σ m:ℂ) = a := by
  constructor
  · intro ha
    by_contra hnone
    have hne (m : ℕ+) (hm : m ≠ n) : (σ m:ℂ) ≠ a := by
      intro he
      exact hnone ⟨m,hm,he⟩
    have hrep : rootReplacement P a (σ n:ℂ) = 0 := by
      apply hillMiura_energy_eq_zero_of_all_original_gap_zeros q hq u c hi hc _
        (analyticOnNhd_rootReplacement P a (σ n:ℂ) hP)
      · intro m
        refine ⟨σ m,hσ m,?_⟩
        by_cases hm : m = n
        · subst m
          exact rootReplacement_zero_new P a (σ n:ℂ)
        · exact rootReplacement_zero_of_ne P a (σ n:ℂ) (σ m:ℂ) ha (hzero m hm) (hne m hm)
      · exact rootReplacement_quadratic_weight_decay P a (σ n:ℂ) (c:ℂ)
          (fun z => -2*sin z) centralCircleRadius tendsto_centralCircleRadius_atTop ha hsmall
    exact hnz (rootReplacement_eq_zero_implies P a (σ n:ℂ) hP ha hrep)
  · rintro ⟨m,hm,he⟩
    rw [← he]
    exact hzero m hm

theorem hillMiura_energy_deriv_ne_zero_at_zero (a : ℂ) (ha : P a = 0) : deriv P a ≠ 0 := by
  intro hd
  have hrep : rootReplacement P a (σ n:ℂ) = 0 := by
    apply hillMiura_energy_eq_zero_of_all_original_gap_zeros q hq u c hi hc _
      (analyticOnNhd_rootReplacement P a (σ n:ℂ) hP)
    · intro m
      refine ⟨σ m,hσ m,?_⟩
      by_cases hm : m = n
      · subst m
        exact rootReplacement_zero_new P a (σ n:ℂ)
      · by_cases he : (σ m:ℂ) = a
        · rw [he]
          exact rootReplacement_zero_of_deriv_zero P a (σ n:ℂ) hd
        · exact rootReplacement_zero_of_ne P a (σ n:ℂ) (σ m:ℂ) ha (hzero m hm) he
    · exact rootReplacement_quadratic_weight_decay P a (σ n:ℂ) (c:ℂ)
        (fun z => -2*sin z) centralCircleRadius tendsto_centralCircleRadius_atTop ha hsmall
  exact hnz (rootReplacement_eq_zero_implies P a (σ n:ℂ) hP ha hrep)

end NLS.KdV
