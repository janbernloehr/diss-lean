import NLS.FunctionalAnalysis.ScalarACVariation
import NLS.FunctionalAnalysis.ScalarL2ExponentialTail

/-! # One-sided Green formulas for globally L2 scalar AC solutions -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Complex
namespace NLS.FunctionalAnalysis

/-- Vanishing forcing on a growing right tail forces the endpoint value to be zero. -/
theorem scalarL2_right_endpoint_eq_zero (α : ℂ) (hα : 0 ≤ α.re)
    (y h : ℝ → ℂ) (hy : MemLp y 2 volume)
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval y a b)
    (hd : ∀ᵐ t : ℝ, HasDerivAt y (α*y t+h t) t) (R : ℝ)
    (hzero : ∀ᵐ t : ℝ, R ≤ t → h t = 0) : y R = 0 := by
  apply scalarL2_right_exponential_coefficient_eq_zero α (y R) R hα y hy
  intro t ht
  apply scalarAC_homogeneous α y R t (hac R t)
  filter_upwards [hd,hzero] with s hs hz
  intro hst
  rw [uIcc_of_le ht] at hst
  simpa only [hz hst.1,add_zero] using hs

/-- Vanishing forcing on a growing left tail forces the endpoint value to be zero. -/
theorem scalarL2_left_endpoint_eq_zero (α : ℂ) (hα : α.re ≤ 0)
    (y h : ℝ → ℂ) (hy : MemLp y 2 volume)
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval y a b)
    (hd : ∀ᵐ t : ℝ, HasDerivAt y (α*y t+h t) t) (R : ℝ)
    (hzero : ∀ᵐ t : ℝ, t ≤ R → h t = 0) : y R = 0 := by
  apply scalarL2_left_exponential_coefficient_eq_zero α (y R) R hα y hy
  intro t ht
  apply scalarAC_homogeneous α y R t (hac R t)
  filter_upwards [hd,hzero] with s hs hz
  intro hst
  rw [uIcc_of_ge ht] at hst
  simpa only [hz hst.2,add_zero] using hs

/-- The right endpoint condition gives the backward one-sided exponential integral. -/
theorem scalarL2_backward_integral (α : ℂ) (hα : 0 ≤ α.re)
    (y h : ℝ → ℂ) (hy : MemLp y 2 volume)
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval y a b)
    (hh : ∀ a b : ℝ, IntervalIntegrable h volume a b)
    (hd : ∀ᵐ t : ℝ, HasDerivAt y (α*y t+h t) t) (R : ℝ)
    (hzero : ∀ᵐ t : ℝ, R ≤ t → h t = 0) (t : ℝ) :
    y t = -(∫ s in t..R, Complex.exp (α*((t-s : ℝ) : ℂ))*h s) := by
  have hR := scalarL2_right_endpoint_eq_zero α hα y h hy hac hd R hzero
  have hi := scalarAC_integratingFactor α y h t R (hac t R) (hh t R)
    (hd.mono (fun _ hs _ => hs))
  rw [hR,mul_zero,zero_sub] at hi
  have hexp (s : ℝ) : Complex.exp (α*((t-s : ℝ) : ℂ)) =
      Complex.exp (α*(t : ℂ))*Complex.exp (-α*(s : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hexp,mul_assoc]
  rw [intervalIntegral.integral_const_mul,hi,mul_neg,neg_neg,← mul_assoc,
    ← Complex.exp_add,neg_mul,add_neg_cancel,Complex.exp_zero,one_mul]

/-- The left endpoint condition gives the forward one-sided exponential integral. -/
theorem scalarL2_forward_integral (α : ℂ) (hα : α.re ≤ 0)
    (y h : ℝ → ℂ) (hy : MemLp y 2 volume)
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval y a b)
    (hh : ∀ a b : ℝ, IntervalIntegrable h volume a b)
    (hd : ∀ᵐ t : ℝ, HasDerivAt y (α*y t+h t) t) (R : ℝ)
    (hzero : ∀ᵐ t : ℝ, t ≤ R → h t = 0) (t : ℝ) :
    y t = ∫ s in R..t, Complex.exp (α*((t-s : ℝ) : ℂ))*h s := by
  have hR := scalarL2_left_endpoint_eq_zero α hα y h hy hac hd R hzero
  simpa only [hR,mul_zero,zero_add] using
    scalarAC_variation α y h R t (hac R t) (hh R t) (hd.mono (fun _ hs _ => hs))

end NLS.FunctionalAnalysis
