import Mathlib.Analysis.Complex.Norm

/-! # Discs with a prescribed real diameter

A function whose zeros are real is nonzero on a diameter circle exactly
when it is nonzero at the real endpoints. This supplies compact contours
for real spectral homotopies without bounding their complex derivatives.
-/

noncomputable section
open Set Metric
namespace NLS.ComplexAnalysis

theorem ofReal_mem_realDiameter_closedBall_iff (a b x : ℝ) :
    (x : ℂ) ∈ closedBall (((a+b)/2 : ℝ) : ℂ) ((b-a)/2) ↔ x ∈ Icc a b := by
  simp only [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    mem_Icc]
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

/-- The open diameter disk corresponds to the strict real interval. -/
theorem ofReal_mem_realDiameter_ball_iff (a b x : ℝ) :
    (x : ℂ) ∈ ball (((a+b)/2 : ℝ) : ℂ) ((b-a)/2) ↔ x ∈ Ioo a b := by
  simp only [mem_ball,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    mem_Ioo]
  rw [abs_lt]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem ofReal_mem_realDiameter_sphere_iff (a b x : ℝ) (hab : a ≤ b) :
    (x : ℂ) ∈ sphere (((a+b)/2 : ℝ) : ℂ) ((b-a)/2) ↔ x = a ∨ x = b := by
  simp only [mem_sphere, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  constructor
  · intro h
    rcases le_total ((a+b)/2) x with hx | hx
    · rw [abs_of_nonneg (by linarith)] at h
      exact Or.inr (by linarith)
    · rw [abs_of_nonpos (by linarith)] at h
      exact Or.inl (by linarith)
  · rintro (rfl | rfl)
    · rw [abs_of_nonpos (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith)]
      ring

/-- For real zeros, excluding the diameter endpoints excludes the entire
circle, including its nonreal part. -/
theorem ne_zero_on_realDiameter_sphere (f : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hreal : ∀ z : ℂ, f z = 0 → z.im = 0) (ha : f a ≠ 0) (hb : f b ≠ 0)
    (z : ℂ) (hz : z ∈ sphere (((a+b)/2 : ℝ) : ℂ) ((b-a)/2)) : f z ≠ 0 := by
  intro hf
  have him := hreal z hf
  have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
  have hzr : z.re = a ∨ z.re = b :=
    (ofReal_mem_realDiameter_sphere_iff a b z.re hab).mp (he.symm ▸ hz)
  rcases hzr with h | h
  · exact ha (by rwa [← he, h] at hf)
  · exact hb (by rwa [← he, h] at hf)

end NLS.ComplexAnalysis
