import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! # The oscillatory integration-by-parts estimate in Appendix G

Absolute continuity suffices for the potential. Endpoint values and
the integral of its derivative give the inverse-frequency bound.
The exponential weight depends only on the real part of the kernel
parameter, so it also covers complex spectral parameters.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
namespace NLS.ComplexAnalysis

/-- The first-iterate kernel: the time variable runs at twice its
original speed because the potential exchanges the two free modes. -/
def oscillatoryKernel (c : ℂ) (t s : ℝ) : ℂ := exp (c*((t-2*s : ℝ) : ℂ))

/-- The scalar oscillatory primitive occurring in the first Born term. -/
def oscillatoryIntegral (c : ℂ) (t : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ s in 0..t, oscillatoryKernel c t s*f s

theorem hasDerivAt_oscillatoryKernel (c : ℂ) (t s : ℝ) :
    HasDerivAt (oscillatoryKernel c t) ((-2*c)*oscillatoryKernel c t s) s := by
  have hd := ((((Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (2 : ℂ)).const_sub (t : ℂ)).const_mul c).cexp
  simp only [Complex.ofRealCLM_apply,Complex.ofReal_one] at hd
  convert hd using 1
  · funext x
    simp [oscillatoryKernel]
  · dsimp only [oscillatoryKernel]
    push_cast
    ring

theorem deriv_oscillatoryKernel (c : ℂ) (t : ℝ) :
    deriv (oscillatoryKernel c t) = fun s => (-2*c)*oscillatoryKernel c t s := by
  funext s
  exact (hasDerivAt_oscillatoryKernel c t s).deriv

/-- Integration by parts, retaining both endpoint terms and the
factor two from the counterpropagating free modes. -/
theorem oscillatoryIntegral_parts (c : ℂ) (t : ℝ) (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 t)
    (hfi : IntervalIntegrable (deriv f) volume 0 t) :
    (2*c)*oscillatoryIntegral c t f =
      exp (c*t)*f 0-exp (-c*t)*f t+oscillatoryIntegral c t (deriv f) := by
  have hk : ContDiff ℝ 1 (oscillatoryKernel c t) := by
    unfold oscillatoryKernel
    have hc : ContDiff ℝ 1 (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.contDiff
    fun_prop
  have hki : IntervalIntegrable (deriv (oscillatoryKernel c t)) volume 0 t := by
    rw [deriv_oscillatoryKernel]
    exact (continuous_const.mul hk.continuous).intervalIntegrable 0 t
  have hi := NLS.FunctionalAnalysis.integral_mul_deriv_eq_complex hf
    hk.contDiffOn.absolutelyContinuousOnInterval hfi hki
  rw [deriv_oscillatoryKernel] at hi
  have he : (fun s => f s*((-2*c)*oscillatoryKernel c t s)) =
      fun s => (-2*c)*(oscillatoryKernel c t s*f s) := by funext s; ring
  have he' : (fun s => deriv f s*oscillatoryKernel c t s) =
      fun s => oscillatoryKernel c t s*deriv f s := by funext s; ring
  rw [he,he',intervalIntegral.integral_const_mul] at hi
  have h0 : oscillatoryKernel c t 0 = exp (c*t) := by simp [oscillatoryKernel]
  have ht : oscillatoryKernel c t t = exp (-c*t) := by
    unfold oscillatoryKernel
    congr 1
    push_cast
    ring
  rw [h0,ht] at hi
  change (-2*c)*oscillatoryIntegral c t f =
    f t*exp (-c*t)-f 0*exp (c*t)-oscillatoryIntegral c t (deriv f) at hi
  linear_combination -hi

/-- The exponentially normalized kernel is at most one throughout
the integration interval, for both signs of the real part. -/
theorem norm_oscillatoryKernel_le (c : ℂ) (t s : ℝ) (hs : s ∈ Icc 0 t) :
    ‖oscillatoryKernel c t s‖ ≤ Real.exp (|c.re| * t) := by
  rw [oscillatoryKernel,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have habs : |t-2*s| ≤ t := abs_le.mpr ⟨by linarith [hs.2],by linarith [hs.1]⟩
  calc
    c.re*(t-2*s) ≤ |c.re*(t-2*s)| := le_abs_self _
    _ = |c.re| * |t-2*s| := abs_mul _ _
    _ ≤ |c.re| * t := mul_le_mul_of_nonneg_left habs (abs_nonneg _)

/-- The inverse-frequency estimate before exponential normalization.
Only an integrable derivative is needed, including at the endpoints. -/
theorem norm_oscillatoryIntegral_le (c : ℂ) (hc : c ≠ 0) (t : ℝ) (ht : 0 ≤ t)
    (f : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 t)
    (hfi : IntervalIntegrable (deriv f) volume 0 t) :
    ‖oscillatoryIntegral c t f‖ ≤
      Real.exp (|c.re| * t)*(‖f 0‖+‖f t‖+∫ s in 0..t, ‖deriv f s‖)/(2*‖c‖) := by
  let E := Real.exp (|c.re| * t)
  have h0 : ‖exp (c*t)‖ ≤ E := by
    simpa only [oscillatoryKernel,mul_zero,sub_zero] using norm_oscillatoryKernel_le c t 0 ⟨le_rfl,ht⟩
  have ht' : ‖exp (-c*t)‖ ≤ E := by
    have h := norm_oscillatoryKernel_le c t t ⟨ht,le_rfl⟩
    convert h using 1
    congr 2
    push_cast
    ring
  have hder : ‖oscillatoryIntegral c t (deriv f)‖ ≤ E*(∫ s in 0..t, ‖deriv f s‖) := by
    rw [← intervalIntegral.integral_const_mul]
    apply norm_integral_le_of_norm_le ht
    · filter_upwards [] with s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_oscillatoryKernel_le c t s ⟨hs.1.le,hs.2⟩) (norm_nonneg _)
    · exact hfi.norm.const_mul E
  apply (le_div_iff₀ (mul_pos (by norm_num) (norm_pos_iff.mpr hc))).mpr
  calc
    ‖oscillatoryIntegral c t f‖*(2*‖c‖) = ‖(2*c)*oscillatoryIntegral c t f‖ := by
      rw [norm_mul,norm_mul,norm_ofNat]
      ring
    _ = ‖exp (c*t)*f 0-exp (-c*t)*f t+oscillatoryIntegral c t (deriv f)‖ := by
      rw [oscillatoryIntegral_parts c t f hf hfi]
    _ ≤ ‖exp (c*t)*f 0‖+‖exp (-c*t)*f t‖+‖oscillatoryIntegral c t (deriv f)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ E*‖f 0‖+E*‖f t‖+E*(∫ s in 0..t, ‖deriv f s‖) := by
      rw [norm_mul,norm_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right h0 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right ht' (norm_nonneg _))) hder
    _ = _ := by dsimp [E]; ring

/-- The exponentially weighted inverse-frequency estimate used in
Appendix G, with the two endpoint terms kept explicit. -/
theorem norm_oscillatoryIntegral_weighted_le (c : ℂ) (hc : c ≠ 0) (t : ℝ) (ht : 0 ≤ t)
    (f : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 t)
    (hfi : IntervalIntegrable (deriv f) volume 0 t) :
    Real.exp (-(|c.re| * t))*‖oscillatoryIntegral c t f‖ ≤
      (‖f 0‖+‖f t‖+∫ s in 0..t, ‖deriv f s‖)/(2*‖c‖) := by
  have h := mul_le_mul_of_nonneg_left (norm_oscillatoryIntegral_le c hc t ht f hf hfi)
    (Real.exp_nonneg (-(|c.re| * t)))
  refine h.trans_eq ?_
  rw [Real.exp_neg]
  field_simp

end NLS.ComplexAnalysis
