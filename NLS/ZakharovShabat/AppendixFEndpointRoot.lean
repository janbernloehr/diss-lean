import NLS.ZakharovShabat.AppendixFRootPath

/-! # The endpoint-spoke square-root formula in F.2

Nonnegative real scaling respects the principal square root. This gives
the literal endpoint-spoke formula, including its initial endpoint,
and the exact positive base radicand without choosing endpoint labels.
-/
noncomputable section
open Complex Set
namespace NLS.ComplexAnalysis

/-- Nonnegative real scaling preserves the principal square-root branch, including zero. -/
theorem appendixF_sqrt_nonnegative_scale (t : ℝ) (ht : 0 ≤ t) (z : ℂ) :
    Complex.sqrt ((t:ℂ)*z) = (Real.sqrt t:ℂ)*Complex.sqrt z := by
  by_cases ht0 : t = 0
  · simp [ht0]
  have h := appendixF_sqrt_positive_scale (Real.sqrt t)
    (Real.sqrt_pos.mpr (lt_of_le_of_ne ht (Ne.symm ht0))) z
  rwa [← Complex.ofReal_pow,Real.sq_sqrt ht] at h

end NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The actual normalized standard root has the literal endpoint-spoke formula for all t >= 0. -/
theorem appendixF_normalized_root_on_endpoint_spoke (ρ₁ ρ₂ ν : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    let τ := (ρ₁+ρ₂)/2
    let z := ρ₁+(t:ℂ)*(ν-ρ₁)
    normalizedStandardRoot τ ((ρ₂-ρ₁)^2) z =
      (τ-z)*(Real.sqrt t:ℂ)*Complex.sqrt ((ρ₁-ν)*(ρ₂-z)/(τ-z)^2) := by
  dsimp only
  let τ := (ρ₁+ρ₂)/2
  let z := ρ₁+(t:ℂ)*(ν-ρ₁)
  change normalizedStandardRoot τ ((ρ₂-ρ₁)^2) z =
    (τ-z)*(Real.sqrt t:ℂ)*Complex.sqrt ((ρ₁-ν)*(ρ₂-z)/(τ-z)^2)
  by_cases hA : τ-z = 0
  · simp only [normalizedStandardRoot,hA,zero_mul]
  have he : 1-(ρ₂-ρ₁)^2/(4*(τ-z)^2) =
      (t:ℂ)*((ρ₁-ν)*(ρ₂-z)/(τ-z)^2) := by
    field_simp
    dsimp [τ,z]
    ring
  rw [normalizedStandardRoot,he,NLS.ComplexAnalysis.appendixF_sqrt_nonnegative_scale t ht]
  ring

/-- At the base source the complex endpoint-spoke radicand is exactly the positive real expression. -/
theorem appendixF_endpoint_base_radicand (ρ₁ ρ₂ : ℂ) (hgap : ρ₂-ρ₁ ≠ 0)
    (σ t : ℝ) (hσ : 0 < σ) (ht : 0 ≤ t) :
    let τ := (ρ₁+ρ₂)/2
    let ν := ρ₁-(σ:ℂ)*(ρ₂-ρ₁)
    let z := ρ₁+(t:ℂ)*(ν-ρ₁)
    (ρ₁-ν)*(ρ₂-z)/(τ-z)^2 =
      ((σ*(1+t*σ)/(1/2+t*σ)^2:ℝ):ℂ) := by
  dsimp only
  have hdR : 0 < (1/2:ℝ)+t*σ := by positivity
  have hd : (((1/2:ℝ)+t*σ:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdR.ne'
  have he : (ρ₁+ρ₂)/2-(ρ₁+(t:ℂ)*(ρ₁-(σ:ℂ)*(ρ₂-ρ₁)-ρ₁)) =
      (((1/2:ℝ)+t*σ:ℝ):ℂ)*(ρ₂-ρ₁) := by push_cast; ring
  rw [he]
  push_cast
  push_cast at hd
  field_simp
  ring

end NLS.ZakharovShabat
