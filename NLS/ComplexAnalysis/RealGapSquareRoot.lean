import NLS.ComplexAnalysis.PrincipalSquareRootSheet
import NLS.ComplexAnalysis.NormalizedAnalyticSquareRoot
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Complex.Convex

/-! # Principal square-root factorization on a real spectral gap

A normalized factor near one fixes the principal root on the closed gap,
including its endpoints and a collapsed gap. No division by the gap is used.
-/
noncomputable section
set_option autoImplicit false
open Complex Set
namespace NLS.ComplexAnalysis

theorem re_pos_of_norm_sub_one_lt_one (w : ℂ) (hw : ‖w-1‖ < 1) : 0 < w.re := by
  have hn := neg_le_abs ((w-1).re)
  have ha := abs_re_le_norm (w-1)
  simp only [sub_re,one_re] at hn ha
  linarith

theorem principalSqrt_nonneg_real_mul_sq (a : ℝ) (ha : 0 ≤ a) (w : ℂ) (hw : 0 < w.re) :
    Complex.sqrt ((a : ℂ)^2*w^2) = (a : ℂ)*w := by
  by_cases hzero : a = 0
  · simp [hzero]
  · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    apply (eq_principalSqrt_of_sq_of_re_pos _ _ (mul_pow _ _ 2) ?_).symm
    simpa only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] using mul_pos hpos hw

theorem continuousAt_principalSqrt_of_re_pos_root (v : ℂ) (hv : 0 < (Complex.sqrt v).re) :
    ContinuousAt Complex.sqrt v := by
  apply Complex.continuousAt_sqrt
  by_cases hi : v.im = 0
  · left
    have hs := complex_sqrt_sq v
    have him := congrArg Complex.im hs
    simp only [pow_two,mul_im,hi] at him
    have hsi : (Complex.sqrt v).im = 0 := by nlinarith
    have hre := congrArg Complex.re hs
    simp only [pow_two,mul_re,hsi,mul_zero,sub_zero] at hre
    nlinarith [sq_nonneg (Complex.sqrt v).re]
  · exact Or.inr hi

theorem ofReal_mem_convex_of_mem_Icc (U : Set ℂ) (hU : Convex ℝ U)
    (l u x : ℝ) (hl : (l : ℂ) ∈ U) (hu : (u : ℂ) ∈ U) (hx : x ∈ Icc l u) :
    (x : ℂ) ∈ U := by
  have hs : x ∈ segment ℝ l u := by
    rw [segment_eq_Icc (hx.1.trans hx.2)]
    exact hx
  have hi : (x : ℂ) ∈ (Complex.ofRealCLM.toLinearMap.toAffineMap) '' segment ℝ l u :=
    ⟨x,hs,rfl⟩
  rw [image_segment] at hi
  exact hU.segment_subset hl hu hi

/-- The actual positive gap weight times a normalized near-one factor
is the principal root of the original quadratic factorization. -/
theorem principalSqrt_real_gap_factor (c l u x : ℝ) (hc : 0 < c)
    (hx : x ∈ Icc l u) (w v : ℂ) (hw : ‖w-1‖ < 1)
    (hv : v = -((x : ℂ)-l)*((x : ℂ)-u)*w^2/(4*(c : ℂ)^2)) :
    Complex.sqrt v = ((Real.sqrt ((x-l)*(u-x))/(2*c) : ℝ) : ℂ)*w := by
  have hp : 0 ≤ (x-l)*(u-x) := mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)
  have hs : (Real.sqrt ((x-l)*(u-x)))^2 = (x-l)*(u-x) := Real.sq_sqrt hp
  have hsq : v = (((Real.sqrt ((x-l)*(u-x))/(2*c) : ℝ) : ℂ)^2)*w^2 := by
    rw [hv]
    push_cast
    have hsC : ((Real.sqrt ((x-l)*(u-x)) : ℂ))^2 = ((x : ℂ)-l)*((u : ℂ)-x) := by
      exact_mod_cast hs
    rw [div_pow,hsC]
    ring
  rw [hsq]
  exact principalSqrt_nonneg_real_mul_sq _ (div_nonneg (Real.sqrt_nonneg _) (by positivity))
    w (re_pos_of_norm_sub_one_lt_one w hw)

theorem continuousAt_principalSqrt_real_gap_factor (c l u x : ℝ) (hc : 0 < c)
    (hx : x ∈ Icc l u) (w v : ℂ) (hw : ‖w-1‖ < 1)
    (hv : v = -((x : ℂ)-l)*((x : ℂ)-u)*w^2/(4*(c : ℂ)^2)) :
    ContinuousAt Complex.sqrt v := by
  have hs := principalSqrt_real_gap_factor c l u x hc hx w v hw hv
  let a : ℝ := Real.sqrt ((x-l)*(u-x))/(2*c)
  change Complex.sqrt v = (a : ℂ)*w at hs
  have ha : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) (by positivity)
  by_cases hz : a = 0
  · have hroot : Complex.sqrt v = 0 := by simpa only [hz,ofReal_zero,zero_mul] using hs
    have hv0 : v = 0 := by rw [← complex_sqrt_sq v,hroot]; simp
    rw [hv0]
    exact Complex.continuousAt_sqrt (Or.inl (by simp))
  · apply continuousAt_principalSqrt_of_re_pos_root
    rw [hs]
    simpa only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] using
      mul_pos (lt_of_le_of_ne ha (Ne.symm hz)) (re_pos_of_norm_sub_one_lt_one w hw)

end NLS.ComplexAnalysis
