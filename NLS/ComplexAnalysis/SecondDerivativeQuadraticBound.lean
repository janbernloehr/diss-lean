import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith

/-! # A quadratic upper bound from a uniformly negative second derivative -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis

/-- Integrate a constant upper bound on the second derivative twice along the unit interval. -/
theorem quadratic_upper_of_second_derivative (f f₁ f₂ : ℝ → ℝ) (c : ℝ)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f₁ (f₂ t) t)
    (hf₂ : ∀ t ∈ Icc (0:ℝ) 1, f₂ t ≤ -c)
    (hzero : f 0 = 0) (hdzero : f₁ 0 = 0) : f 1 ≤ -c/2 := by
  let g := fun t : ℝ => f t+(c/2)*t^2
  let g₁ := fun t : ℝ => f₁ t+c*t
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt g (g₁ t) t := by
    have hp : HasDerivAt (fun x : ℝ => (c/2)*x^2) (c*t) t := by
      convert! (((hasDerivAt_id t).pow 2).const_mul (c/2)) using 1
      simp only [id_eq]
      ring
    simpa only [g,g₁] using! (hf t ht).add hp
  have hd₁ (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt g₁ (f₂ t+c) t := by
    simpa only [g₁,mul_one] using! (hf₁ t ht).add ((hasDerivAt_id t).const_mul c)
  have hanti₁ : AntitoneOn g₁ (Icc (0:ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t ht => (hd₁ t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd₁ t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => by linarith [hf₂ t (interior_subset ht)])
  have hanti : AntitoneOn g (Icc (0:ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => by
        have h := hanti₁ (show (0:ℝ) ∈ Icc 0 1 by norm_num) (interior_subset ht) (interior_subset ht).1
        simpa only [g₁,hdzero,mul_zero,add_zero] using h)
  have h := hanti (show (0:ℝ) ∈ Icc 0 1 by norm_num) (show (1:ℝ) ∈ Icc 0 1 by norm_num) zero_le_one
  dsimp [g] at h
  rw [hzero] at h
  nlinarith

end NLS.ComplexAnalysis
