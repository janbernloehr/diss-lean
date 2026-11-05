import NLS.ComplexAnalysis.ComplexArcsineIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The normalized semicircle mean

The literal square-root gap weight becomes a sine-square cosine profile.
Its mass is exactly pi over two, giving an error bound with constant one.
-/
noncomputable section
set_option autoImplicit false
open Set Real Complex MeasureTheory
namespace NLS.ComplexAnalysis

def normalizedSemicircleMean (f : ℝ → ℂ) : ℂ :=
  (2/(Real.pi : ℂ)) * ∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*f (Real.cos θ)

theorem integral_sineSquare_complex :
    (∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2) = (Real.pi : ℂ)/2 := by
  rw [show (fun θ : ℝ => (Real.sin θ : ℂ)^2) = fun θ => (((Real.sin θ)^2 : ℝ) : ℂ) by
    funext θ; simp, intervalIntegral.integral_ofReal]
  simp

theorem integral_semicircle_eq_sineSquare (f : ℝ → ℂ) :
    (∫ t in (-1 : ℝ)..1, (Real.sqrt (1-t^2) : ℂ)*f t) =
      ∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*f (Real.cos θ) := by
  calc
    _ = ∫ t in (-1 : ℝ)..1, ((1-t^2 : ℝ) : ℂ)*f t/(Real.sqrt (1-t^2) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      have htle : -1 ≤ t ∧ t ≤ 1 := by simpa using ht
      have hp : 0 ≤ 1-t^2 := by nlinarith [htle.1,htle.2]
      have hs : ((Real.sqrt (1-t^2) : ℂ))^2 = ((1-t^2 : ℝ) : ℂ) := by
        exact_mod_cast Real.sq_sqrt hp
      rw [← hs]
      by_cases hz : (Real.sqrt (1-t^2) : ℂ) = 0
      · simp [hz]
      · field_simp
    _ = ∫ θ in (0 : ℝ)..Real.pi, ((1-(Real.cos θ)^2 : ℝ) : ℂ)*f (Real.cos θ) :=
      integral_div_sqrt_one_sub_sq_eq_cosine _
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      have he : 1-(Real.cos θ)^2 = (Real.sin θ)^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
      rw [he,Complex.ofReal_pow]

theorem norm_normalizedSemicircleMean_sub_one_le (f : ℝ → ℂ) (epsilon : ℝ)
    (hf : ContinuousOn f (Icc (-1) 1))
    (he : ∀ t ∈ Icc (-1) 1, ‖f t-1‖ ≤ epsilon) :
    ‖normalizedSemicircleMean f-1‖ ≤ epsilon := by
  have hc : ContinuousOn (fun θ : ℝ => f (Real.cos θ)) (Icc 0 Real.pi) :=
    hf.comp Real.continuous_cos.continuousOn
      (fun θ _ => ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩)
  have hi : IntervalIntegrable (fun θ : ℝ => (Real.sin θ : ℂ)^2*f (Real.cos θ)) volume 0 Real.pi :=
    (((Complex.continuous_ofReal.comp Real.continuous_sin).pow 2).continuousOn.mul hc).intervalIntegrable_of_Icc
      Real.pi_pos.le
  have hs : IntervalIntegrable (fun θ : ℝ => (Real.sin θ : ℂ)^2) volume 0 Real.pi :=
    ((Complex.continuous_ofReal.comp Real.continuous_sin).pow 2).intervalIntegrable _ _
  have hsub : normalizedSemicircleMean f-1 = (2/(Real.pi : ℂ)) *
      (∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*(f (Real.cos θ)-1)) := by
    rw [show (fun θ : ℝ => (Real.sin θ : ℂ)^2*(f (Real.cos θ)-1)) =
      fun θ => (Real.sin θ : ℂ)^2*f (Real.cos θ)-(Real.sin θ : ℂ)^2 by funext θ; ring,
      intervalIntegral.integral_sub hi hs,integral_sineSquare_complex]
    dsimp only [normalizedSemicircleMean]
    field_simp
  have hb : ‖∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*(f (Real.cos θ)-1)‖ ≤
      Real.pi/2*epsilon := by
    have hg : IntervalIntegrable (fun θ : ℝ => (Real.sin θ)^2*epsilon) volume 0 Real.pi :=
      ((Real.continuous_sin.pow 2).mul continuous_const).intervalIntegrable _ _
    have hh := intervalIntegral.norm_integral_le_of_norm_le Real.pi_pos.le
      (f := fun θ : ℝ => (Real.sin θ : ℂ)^2*(f (Real.cos θ)-1))
      (g := fun θ : ℝ => (Real.sin θ)^2*epsilon) (Filter.Eventually.of_forall fun θ _ => by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
        exact mul_le_mul_of_nonneg_left (he _ ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩) (sq_nonneg _)) hg
    simpa only [intervalIntegral.integral_mul_const,integral_sin_sq,Real.sin_zero,Real.cos_zero,
      Real.sin_pi,Real.cos_pi,mul_zero,zero_mul,sub_zero,zero_add] using hh
  rw [hsub,norm_mul]
  have hn : ‖(2 : ℂ)/(Real.pi : ℂ)‖ = 2/Real.pi := by simp [abs_of_pos Real.pi_pos]
  rw [hn]
  calc
    _ ≤ (2/Real.pi)*(Real.pi/2*epsilon) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = epsilon := by field_simp

end NLS.ComplexAnalysis
