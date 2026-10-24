import NLS.FunctionalAnalysis.ScaledCutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Integral bounds for compact cutoffs of a continuous mass density -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace NLS.FunctionalAnalysis

theorem integrable_sq_norm_cutoff (χ : ℝ → ℂ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) : Integrable (fun t => ‖χ t‖ ^ 2) := by
  have hs : HasCompactSupport (fun t => ‖χ t‖ ^ 2) := by
    simpa only [Function.comp_def] using! hc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  exact (hχ.norm.pow 2).integrable_of_hasCompactSupport hs

theorem integrable_cutoff_mass (χ : ℝ → ℂ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (m : ℝ → ℝ) (hm : Continuous m) :
    Integrable (fun t => ‖χ t‖ ^ 2 * m t) := by
  have hs : HasCompactSupport (fun t => ‖χ t‖ ^ 2) := by
    simpa only [Function.comp_def] using! hc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  exact ((hχ.norm.pow 2).mul hm).integrable_of_hasCompactSupport hs.mul_right

/-- A cutoff equal to one on an interval retains all mass of that interval. -/
theorem interval_mass_le_cutoff_mass (χ : ℝ → ℂ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (m : ℝ → ℝ) (hm : Continuous m)
    (hm0 : ∀ t, 0 ≤ m t) (R : ℝ) (hR : 0 ≤ R)
    (hone : ∀ t ∈ Icc 0 R, χ t = 1) :
    (∫ t in (0 : ℝ)..R, m t) ≤ ∫ t : ℝ, ‖χ t‖ ^ 2 * m t := by
  rw [intervalIntegral.integral_of_le hR]
  calc
    (∫ t in Ioc (0 : ℝ) R, m t) = ∫ t in Ioc (0 : ℝ) R, ‖χ t‖ ^ 2 * m t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change m t = ‖χ t‖ ^ 2 * m t
      rw [hone t ⟨ht.1.le,ht.2⟩,norm_one,one_pow,one_mul]
    _ ≤ _ := setIntegral_le_integral (integrable_cutoff_mass χ hχ hc m hm)
      (Filter.Eventually.of_forall (fun t => mul_nonneg (sq_nonneg _) (hm0 t)))

/-- A uniform upper bound for the density controls the derivative-weighted mass. -/
theorem derivative_cutoff_mass_le (χ : ℝ → ℂ) (hχ : ContDiff ℝ 1 χ)
    (hc : HasCompactSupport χ) (m : ℝ → ℝ) (hm : Continuous m)
    (B : ℝ) (hB : ∀ t, m t ≤ B) :
    (∫ t : ℝ, ‖deriv χ t‖ ^ 2 * m t) ≤ B * ∫ t : ℝ, ‖deriv χ t‖ ^ 2 := by
  rw [← integral_const_mul]
  apply integral_mono
    (integrable_cutoff_mass _ hχ.continuous_deriv_one hc.deriv m hm)
    ((integrable_sq_norm_cutoff _ hχ.continuous_deriv_one hc.deriv).const_mul B)
  intro t
  simpa only [mul_comm B] using mul_le_mul_of_nonneg_left (hB t) (sq_nonneg _)

/-- Dilation makes the derivative-weighted mass uniformly bounded for scales at least one. -/
theorem scaled_derivative_cutoff_mass_le (χ : ℝ → ℂ) (hχ : ContDiff ℝ 1 χ)
    (hc : HasCompactSupport χ) (m : ℝ → ℝ) (hm : Continuous m)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ t, m t ≤ B) (R : ℝ) (hR : 1 ≤ R) :
    (∫ t : ℝ, ‖deriv (scaledCutoff χ R) t‖ ^ 2 * m t) ≤
      B * ∫ t : ℝ, ‖deriv χ t‖ ^ 2 := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  calc
    _ ≤ B * ∫ t : ℝ, ‖deriv (scaledCutoff χ R) t‖ ^ 2 :=
      derivative_cutoff_mass_le _ (contDiff_scaledCutoff χ hχ R)
        (hasCompactSupport_scaledCutoff χ hc R hRp.ne') m hm B hB
    _ = B * ((∫ t : ℝ, ‖deriv χ t‖ ^ 2) / R) := by
      rw [integral_sq_deriv_scaledCutoff χ hχ R hRp]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_self (integral_nonneg (fun t => sq_nonneg _)) hR) hB0

end NLS.FunctionalAnalysis
