import NLS.ZakharovShabat.ClassicalFirstBornBound
import NLS.FunctionalAnalysis.IntegralGronwall
import NLS.ComplexAnalysis.NormalizedDuhamelBound

/-! # Full fundamental-solution error from its first oscillatory iterate

The same exponential normalization applies inside the Volterra
integral. Integral Gronwall closes the estimate without an assumed
bound on the actual error, uniformly in the real spectral frequency.
-/

noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The actual solution error in the exponentially weighted norm
used in Appendix G. -/
def classicalNormalizedRemainder (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : ℝ) : ℝ :=
  Real.exp (-(|z.im| * t))*‖classicalSolutionRemainder φ z v t‖

theorem continuous_classicalNormalizedRemainder (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    Continuous (classicalNormalizedRemainder φ z v) :=
  (show Continuous (fun t : ℝ => Real.exp (-(|z.im| * t))) by fun_prop).mul
    (continuous_classicalSolutionRemainder φ z v).norm

theorem classicalNormalizedRemainder_nonneg (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : ℝ) :
    0 ≤ classicalNormalizedRemainder φ z v t := mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)

/-- The actual pair error satisfies the normalized scalar Volterra
inequality, with the potential supremum as coupling constant. -/
theorem classicalNormalizedRemainder_le_firstBorn_add_integral
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalNormalizedRemainder φ z v t ≤
      Real.exp (-(|z.im| * t.val))*‖classicalFirstBornVector φ z v t‖+
        ‖φ‖*(∫ s in (0 : ℝ)..t.val, classicalNormalizedRemainder φ z v s) := by
  let R := classicalSolutionRemainder φ z v
  let E := Real.exp (-(|z.im| * t.val))
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hr : Continuous (fun s : ℝ => ‖φ‖*‖R s‖) :=
    continuous_const.mul (continuous_classicalSolutionRemainder φ z v).norm
  have hfst : E*‖∫ s in (0 : ℝ)..t.val, exp (-I*z*(t.val-s))*(I*(extend φ s).1*(R s).2)‖ ≤
      ‖φ‖*(∫ s in (0 : ℝ)..t.val, classicalNormalizedRemainder φ z v s) := by
    have h := norm_exp_integral_weighted_le (-I*z) |z.im| t
      (by simpa [Complex.mul_re] using le_abs_self z.im) t.property.1
      (fun s => I*(extend φ s).1*(R s).2) (fun s => ‖φ‖*‖R s‖) hr (by
        intro s _
        simp only [norm_mul,norm_I,one_mul]
        exact mul_le_mul ((norm_fst_le (extend φ s)).trans (φ.norm_coe_le_norm _))
          (norm_snd_le (R s)) (norm_nonneg _) (norm_nonneg _))
    have he : (fun s : ℝ => Real.exp (-|z.im| * s)*(‖φ‖*‖R s‖)) =
        fun s => ‖φ‖*classicalNormalizedRemainder φ z v s := by
      funext s
      dsimp only [classicalNormalizedRemainder,R]
      rw [neg_mul]
      ring
    rw [he,intervalIntegral.integral_const_mul] at h
    simpa only [Complex.ofReal_sub,neg_mul] using h
  have hsnd : E*‖∫ s in (0 : ℝ)..t.val, exp (I*z*(t.val-s))*((-I)*(extend φ s).2*(R s).1)‖ ≤
      ‖φ‖*(∫ s in (0 : ℝ)..t.val, classicalNormalizedRemainder φ z v s) := by
    have h := norm_exp_integral_weighted_le (I*z) |z.im| t
      (by simpa [Complex.mul_re] using neg_le_abs z.im) t.property.1
      (fun s => (-I)*(extend φ s).2*(R s).1) (fun s => ‖φ‖*‖R s‖) hr (by
        intro s _
        simp only [norm_mul,norm_neg,norm_I,one_mul]
        exact mul_le_mul ((norm_snd_le (extend φ s)).trans (φ.norm_coe_le_norm _))
          (norm_fst_le (R s)) (norm_nonneg _) (norm_nonneg _))
    have he : (fun s : ℝ => Real.exp (-|z.im| * s)*(‖φ‖*‖R s‖)) =
        fun s => ‖φ‖*classicalNormalizedRemainder φ z v s := by
      funext s
      dsimp only [classicalNormalizedRemainder,R]
      rw [neg_mul]
      ring
    rw [he,intervalIntegral.integral_const_mul] at h
    simpa only [Complex.ofReal_sub,neg_mul] using h
  change E*‖R t‖ ≤ _
  rw [Prod.norm_def,mul_max_of_nonneg _ _ hE]
  apply max_le
  · change E*‖(classicalSolutionRemainder φ z v t).1‖ ≤ _
    rw [classicalSolutionRemainder_fst_duhamel]
    exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) hE).trans
      (by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le _) hE) hfst)
  · change E*‖(classicalSolutionRemainder φ z v t).2‖ ≤ _
    rw [classicalSolutionRemainder_snd_duhamel]
    exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) hE).trans
      (by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_left (norm_snd_le _) hE) hsnd)

/-- A uniform first-iterate bound controls the full actual error at
every time. No smallness restriction on the potential is imposed. -/
theorem classicalNormalizedRemainder_le_of_firstBorn_bound
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hfirst : ∀ t : Icc (0 : ℝ) 1,
      Real.exp (-(|z.im| * t.val))*‖classicalFirstBornVector φ z v t‖ ≤ A)
    (t : Icc (0 : ℝ) 1) :
    classicalNormalizedRemainder φ z v t ≤ A*Real.exp (‖φ‖*t.val) := by
  apply NLS.FunctionalAnalysis.le_exp_of_le_const_add_integral
    (classicalNormalizedRemainder φ z v) (continuous_classicalNormalizedRemainder φ z v)
    1 A ‖φ‖ hA (norm_nonneg _) (fun s _ => classicalNormalizedRemainder_nonneg φ z v s)
    (fun s hs => (classicalNormalizedRemainder_le_firstBorn_add_integral φ z v ⟨s,hs⟩).trans
      (add_le_add (hfirst ⟨s,hs⟩) le_rfl)) t.val t.property

/-- The full actual fundamental-solution error has inverse-frequency
decay under the endpoint/derivative budget, uniformly on the unit interval. -/
theorem classicalNormalizedRemainder_le_inverse_frequency
    (φ : Curve (ℂ × ℂ))
    (hf : AbsolutelyContinuousOnInterval (fun s => (extend φ s).1) 0 1)
    (hg : AbsolutelyContinuousOnInterval (fun s => (extend φ s).2) 0 1)
    (hfi : IntervalIntegrable (deriv (fun s => (extend φ s).1)) volume 0 1)
    (hgi : IntervalIntegrable (deriv (fun s => (extend φ s).2)) volume 0 1)
    (z : ℂ) (hz : z ≠ 0) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalNormalizedRemainder φ z v t ≤
      classicalFirstBornUniformBudget φ*‖v‖/(2*‖z‖)*Real.exp ‖φ‖ := by
  have hB := classicalFirstBornUniformBudget_nonneg φ
  have h := classicalNormalizedRemainder_le_of_firstBorn_bound φ z v
    (classicalFirstBornUniformBudget φ*‖v‖/(2*‖z‖)) (by positivity)
    (norm_classicalFirstBornVector_weighted_uniform_le φ hf hg hfi hgi z hz v) t
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (by nlinarith [norm_nonneg φ,t.property.2])) (by positivity))

end NLS.ZakharovShabat
