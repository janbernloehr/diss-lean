import NLS.ZakharovShabat.SourceNormalizedActionEstimate

/-! # The factor-nine cosine estimate underlying equation (5.15) -/
noncomputable section
open Complex MeasureTheory
namespace NLS.ZakharovShabat

/-- The exact norm-square cosine moment also holds for a complex offset. -/
theorem integral_norm_shifted_cos_sq (u : ℂ) :
    (∫ θ in (0:ℝ)..Real.pi, ‖u-(Real.cos θ:ℂ)‖^2) = Real.pi*(‖u‖^2+1/2) := by
  have hpoint (θ : ℝ) : ‖u-(Real.cos θ:ℂ)‖^2 = (u.re-Real.cos θ)^2+u.im^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.ofReal_re,
      Complex.sub_im,Complex.ofReal_im,sub_zero]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun θ : ℝ => (u.re-Real.cos θ)^2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun _ : ℝ => u.im^2)).intervalIntegrable _ _),
    integral_shifted_cos_sq,intervalIntegral.integral_const]
  simp only [sub_zero,smul_eq_mul,Complex.sq_norm,Complex.normSq_apply]
  ring

/-- A bound on the complementary factor controls the exact normalized cosine model. -/
theorem norm_normalizedActionCosineModel_le_factor (u : ℂ) (χ : ℝ → ℂ)
    (hχ : Continuous χ) (K : ℝ)
    (hK : ∀ θ ∈ Set.Icc 0 Real.pi, ‖χ θ‖ ≤ K) :
    ‖normalizedActionCosineModel u χ‖ ≤ (1+2*‖u‖^2)*K := by
  have hweight : Continuous (fun θ : ℝ => ‖u-(Real.cos θ:ℂ)‖^2) := by fun_prop
  have hInt : ‖∫ θ in (0:ℝ)..Real.pi, (u-(Real.cos θ:ℂ))^2*χ θ‖ ≤
      (Real.pi*(‖u‖^2+1/2))*K := by
    calc
      _ ≤ ∫ θ in (0:ℝ)..Real.pi, ‖(u-(Real.cos θ:ℂ))^2*χ θ‖ :=
        intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le
      _ ≤ ∫ θ in (0:ℝ)..Real.pi, ‖u-(Real.cos θ:ℂ)‖^2*K := by
        apply intervalIntegral.integral_mono_on Real.pi_pos.le
          ((by fun_prop : Continuous (fun θ : ℝ => ‖(u-(Real.cos θ:ℂ))^2*χ θ‖)).intervalIntegrable _ _)
          ((hweight.mul continuous_const).intervalIntegrable _ _)
        intro θ hθ
        simp only [norm_mul,norm_pow]
        exact mul_le_mul_of_nonneg_left (hK θ hθ) (sq_nonneg _)
      _ = _ := by rw [intervalIntegral.integral_mul_const,integral_norm_shifted_cos_sq]
  rw [normalizedActionCosineModel,norm_mul]
  have hcoef : ‖(2/(Real.pi:ℂ))‖ = 2/Real.pi := by simp [abs_of_pos Real.pi_pos]
  rw [hcoef]
  calc
    _ ≤ (2/Real.pi)*((Real.pi*(‖u‖^2+1/2))*K) :=
      mul_le_mul_of_nonneg_left hInt (by positivity)
    _ = _ := by field_simp; ring

/-- The printed factor nine follows from a normalized critical offset of norm at most two. -/
theorem norm_normalizedActionCosineModel_le_nine (u : ℂ) (χ : ℝ → ℂ)
    (hχ : Continuous χ) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ θ ∈ Set.Icc 0 Real.pi, ‖χ θ‖ ≤ K) (hu : ‖u‖ ≤ 2) :
    ‖normalizedActionCosineModel u χ‖ ≤ 9*K := by
  have hs : ‖u‖^2 ≤ 4 := by nlinarith [norm_nonneg u]
  exact (norm_normalizedActionCosineModel_le_factor u χ hχ K hbound).trans
    (mul_le_mul_of_nonneg_right (by linarith) hK)

/-- On a real gap the critical point lies inside the gap, improving nine to three. -/
theorem norm_normalizedActionCosineModel_le_three (u : ℂ) (χ : ℝ → ℂ)
    (hχ : Continuous χ) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ θ ∈ Set.Icc 0 Real.pi, ‖χ θ‖ ≤ K) (hu : ‖u‖ ≤ 1) :
    ‖normalizedActionCosineModel u χ‖ ≤ 3*K := by
  have hs : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  exact (norm_normalizedActionCosineModel_le_factor u χ hχ K hbound).trans
    (mul_le_mul_of_nonneg_right (by linarith) hK)

end NLS.ZakharovShabat
