import NLS.ComplexAnalysis.WeightedDuhamelIntegralBounds

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
namespace NLS.ComplexAnalysis

/-- The cosine Volterra kernel has its true exponential weight; weights
cancel on the integration triangle, uniformly in the imaginary frequency. -/
theorem norm_cosine_duhamel_integral_le_weighted (q u : ℝ → ℂ) (z : ℂ) (B t : ℝ)
    (hq : Continuous q) (ht : 0 ≤ t)
    (hu : ∀ s ∈ Icc 0 t, ‖u s‖ ≤ Real.exp (|z.im| * s) * B) :
    ‖∫ s in (0:ℝ)..t, cos (z * ((t-s:ℝ):ℂ)) * q s * u s‖ ≤
      (Real.exp (|z.im| * t) * B) * (∫ s in (0:ℝ)..t, ‖q s‖) := by
  have hb (s : ℝ) (hs : s ∈ Icc (0:ℝ) t) :
      ‖cos (z * ((t-s:ℝ):ℂ)) * q s * u s‖ ≤
        (Real.exp (|z.im| * t) * B) * ‖q s‖ := by
    have htr := (norm_trig_mul_real_weighted_le z |z.im| (t-s) le_rfl (sub_nonneg.mpr hs.2)).1
    rw [norm_mul,norm_mul]
    have hh := mul_le_mul htr (hu s hs) (norm_nonneg _) (Real.exp_pos (|z.im| * (t-s))).le
    have he : Real.exp (|z.im| * (t-s)) * (Real.exp (|z.im| * s) * B) =
        Real.exp (|z.im| * t) * B := by
      rw [←mul_assoc,←Real.exp_add,show |z.im| * (t-s) + |z.im| * s = |z.im| * t by ring]
    rw [he] at hh
    nlinarith [mul_le_mul_of_nonneg_right hh (norm_nonneg (q s))]
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht
    (Filter.Eventually.of_forall (fun s hs => hb s ⟨hs.1.le,hs.2⟩))
    ((continuous_const.mul hq.norm).intervalIntegrable 0 t)
  simpa only [intervalIntegral.integral_const_mul] using hi

end NLS.ComplexAnalysis
