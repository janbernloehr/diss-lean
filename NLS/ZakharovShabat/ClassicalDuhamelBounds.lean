import NLS.ZakharovShabat.ClassicalDuhamel
import NLS.ComplexAnalysis.DecayingDuhamelKernel

/-!
# Decaying-coordinate bounds for classical solutions

The error from the free coordinate is bounded by the potential supremum norm
times a bound for the opposite weighted coordinate, divided by the decay rate.
The upper and lower half-plane rates are exactly twice the imaginary height.
Bounds on the opposite coordinate remain explicit hypotheses here.
-/

noncomputable section
open Set Complex intervalIntegral
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

theorem norm_classicalWeightedSolution_fst_sub_free_le (φ : Curve (ℂ × ℂ))
    (z c : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) (a B : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) (hc : (c - I*z).re = -a)
    (hb : ∀ s : Icc (0 : ℝ) 1, ‖(classicalWeightedSolution φ z c v s).2‖ ≤ B) :
    ‖(classicalWeightedSolution φ z c v t).1 - exp ((c - I*z) * t.val) * v.1‖ ≤
      ‖φ‖ * B / a := by
  rw [classicalWeightedSolution_fst_duhamel, add_sub_cancel_left]
  apply norm_integral_exp_propagator_mul_le (c - I*z) a t.val (‖φ‖ * B)
    ha t.property.1 (mul_nonneg (norm_nonneg _) hB) hc
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans t.property.2⟩
  have hp := (norm_fst_le (φ ⟨s, hs'⟩)).trans (φ.norm_coe_le_norm ⟨s, hs'⟩)
  simp only [NLS.LinearVolterra.extend, projIcc_of_mem _ hs', norm_mul,
    Complex.norm_I, one_mul]
  exact mul_le_mul hp (hb ⟨s, hs'⟩) (norm_nonneg _) (norm_nonneg _)

theorem norm_classicalWeightedSolution_snd_sub_free_le (φ : Curve (ℂ × ℂ))
    (z c : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) (a B : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) (hc : (c + I*z).re = -a)
    (hb : ∀ s : Icc (0 : ℝ) 1, ‖(classicalWeightedSolution φ z c v s).1‖ ≤ B) :
    ‖(classicalWeightedSolution φ z c v t).2 - exp ((c + I*z) * t.val) * v.2‖ ≤
      ‖φ‖ * B / a := by
  rw [classicalWeightedSolution_snd_duhamel, add_sub_cancel_left]
  apply norm_integral_exp_propagator_mul_le (c + I*z) a t.val (‖φ‖ * B)
    ha t.property.1 (mul_nonneg (norm_nonneg _) hB) hc
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans t.property.2⟩
  have hp := (norm_snd_le (φ ⟨s, hs'⟩)).trans (φ.norm_coe_le_norm ⟨s, hs'⟩)
  simp only [NLS.LinearVolterra.extend, projIcc_of_mem _ hs', norm_mul,
    norm_neg, Complex.norm_I, one_mul]
  exact mul_le_mul hp (hb ⟨s, hs'⟩) (norm_nonneg _) (norm_nonneg _)

/-- The upper-half-plane error has the exact inverse-height factor. -/
theorem norm_classicalWeightedSolution_upper_snd_sub_free_le (φ : Curve (ℂ × ℂ))
    (z : ℂ) (hz : 0 < z.im) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) (B : ℝ)
    (hB : 0 ≤ B)
    (hb : ∀ s : Icc (0 : ℝ) 1, ‖(classicalWeightedSolution φ z (I*z) v s).1‖ ≤ B) :
    ‖(classicalWeightedSolution φ z (I*z) v t).2 - exp ((2*I*z) * t.val) * v.2‖ ≤
      ‖φ‖ * B / (2*z.im) := by
  have h := norm_classicalWeightedSolution_snd_sub_free_le φ z (I*z) v t (2*z.im) B
    (by positivity) hB (by simp [Complex.mul_re]; ring) hb
  simpa only [show I*z + I*z = 2*I*z by ring] using h

/-- The lower-half-plane error has the same positive inverse-height factor. -/
theorem norm_classicalWeightedSolution_lower_fst_sub_free_le (φ : Curve (ℂ × ℂ))
    (z : ℂ) (hz : z.im < 0) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) (B : ℝ)
    (hB : 0 ≤ B)
    (hb : ∀ s : Icc (0 : ℝ) 1, ‖(classicalWeightedSolution φ z (-I*z) v s).2‖ ≤ B) :
    ‖(classicalWeightedSolution φ z (-I*z) v t).1 - exp ((-2*I*z) * t.val) * v.1‖ ≤
      ‖φ‖ * B / (-2*z.im) := by
  have h := norm_classicalWeightedSolution_fst_sub_free_le φ z (-I*z) v t (-2*z.im) B
    (mul_pos_of_neg_of_neg (by norm_num) hz) hB (by simp [Complex.mul_re]; ring) hb
  simpa only [show -I*z - I*z = -2*I*z by ring] using h

end NLS.ZakharovShabat
