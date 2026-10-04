import NLS.ZakharovShabat.SourceStandardRootGapSideIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exact polynomial gap-side integrals

The leading terms in Lemma 20.3 reduce to the quadratic root polynomial
and its product with a centered linear factor. Cosine coordinates prove
the exact constants for arbitrary complex gaps, including collapsed ones.
-/
noncomputable section
open Complex MeasureTheory intervalIntegral
namespace NLS.ZakharovShabat

/-- A quadratic numerator divided by the side root integrates to the
semicircle area, with the sign fixed by the chosen gap side. -/
theorem gapSideBoundaryIntegral_quadratic (τ δ : ℂ) (upper : Bool) :
    gapSideBoundaryIntegral τ δ (fun z => (z-τ)^2-δ^2) 1 upper =
      -(if upper then I else -I) * (Real.pi:ℂ) * δ^2 / 2 := by
  by_cases hδ : δ = 0
  · subst δ
    simp [gapSideBoundaryIntegral]
  rw [gapSideBoundaryIntegral_eq_primitive τ δ _ 1 hδ upper]
  have hfun : (fun θ : ℝ => (τ+δ*(Real.cos θ:ℂ)-τ)^2-δ^2) =
      fun θ : ℝ => δ^2 * ((Real.cos θ)^2-1:ℝ) := by
    funext θ
    push_cast
    ring
  simp only [gapSidePrimitive,Real.arccos_one,hfun,intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_ofReal,intervalIntegral.integral_sub ((by fun_prop : Continuous (fun θ : ℝ => Real.cos θ ^ 2)).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _)]
  simp only [integral_cos_sq,Real.cos_pi,Real.sin_pi,Real.cos_zero,Real.sin_zero,
    mul_zero,sub_zero,zero_add,intervalIntegral.integral_const,smul_eq_mul,mul_one]
  push_cast
  ring

/-- The centered odd correction has exactly zero integral. -/
theorem gapSideBoundaryIntegral_centered_quadratic (τ δ : ℂ) (upper : Bool) :
    gapSideBoundaryIntegral τ δ (fun z => (τ-z)*((z-τ)^2-δ^2)) 1 upper = 0 := by
  by_cases hδ : δ = 0
  · subst δ
    simp [gapSideBoundaryIntegral]
  rw [gapSideBoundaryIntegral_eq_primitive τ δ _ 1 hδ upper]
  have hfun : (fun θ : ℝ => (τ-(τ+δ*(Real.cos θ:ℂ)))*((τ+δ*(Real.cos θ:ℂ)-τ)^2-δ^2)) =
      fun θ : ℝ => δ^3 * (Real.cos θ-(Real.cos θ)^3:ℝ) := by
    funext θ
    push_cast
    ring
  simp only [gapSidePrimitive,Real.arccos_one,hfun,intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_ofReal,intervalIntegral.integral_sub (Real.continuous_cos.intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun θ : ℝ => Real.cos θ ^ 3)).intervalIntegrable _ _)]
  simp

/-- The shifted linear numerator leaves only its displacement from the
midpoint; the odd contribution cancels exactly. -/
theorem gapSideBoundaryIntegral_shifted_quadratic (τ δ σ : ℂ) (upper : Bool) :
    gapSideBoundaryIntegral τ δ (fun z => (σ-z)*((z-τ)^2-δ^2)) 1 upper =
      -(if upper then I else -I) * (Real.pi:ℂ) * δ^2 * (σ-τ) / 2 := by
  by_cases hδ : δ = 0
  · subst δ
    simp [gapSideBoundaryIntegral]
  have hfun : (fun θ : ℝ => (σ-(τ+δ*(Real.cos θ:ℂ)))*((τ+δ*(Real.cos θ:ℂ)-τ)^2-δ^2)) =
      fun θ : ℝ => (σ-τ)*((τ+δ*(Real.cos θ:ℂ)-τ)^2-δ^2) +
        (τ-(τ+δ*(Real.cos θ:ℂ)))*((τ+δ*(Real.cos θ:ℂ)-τ)^2-δ^2) := by
    funext θ
    ring
  have hquad := gapSideBoundaryIntegral_quadratic τ δ upper
  have hodd := gapSideBoundaryIntegral_centered_quadratic τ δ upper
  rw [gapSideBoundaryIntegral_eq_primitive τ δ _ 1 hδ upper] at hquad hodd ⊢
  simp only [gapSidePrimitive,Real.arccos_one] at hquad hodd ⊢
  rw [hfun,intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun θ : ℝ => (σ-τ)*((τ+δ*(Real.cos θ:ℂ)-τ)^2-δ^2))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun θ : ℝ => (τ-(τ+δ*(Real.cos θ:ℂ)))*((τ+δ*(Real.cos θ:ℂ)-τ)^2-δ^2))).intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  linear_combination (σ-τ)*hquad + hodd

end NLS.ZakharovShabat
