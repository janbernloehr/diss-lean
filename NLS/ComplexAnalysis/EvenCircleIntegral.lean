import NLS.ComplexAnalysis.CircleIntegralReflection

/-! Even scalar integrands have opposite periods on reflected circles,
and zero period on every circle centered at zero. -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem circleIntegral_even_neg_center (f : ℂ → ℂ) (hf : ∀ z : ℂ, f (-z) = f z) (c : ℂ) (R : ℝ) :
    (∮ z in C(-c,R), f z) = -(∮ z in C(c,R), f z) := by
  have h := circleIntegral_neg_pullback f c R
  simp_rw [hf] at h
  have hn : (fun z : ℂ => -f z) = (fun z => (-1:ℂ)*f z) := by funext z; ring
  rw [hn,circleIntegral.integral_const_mul,neg_one_mul] at h
  exact h.symm

theorem circleIntegral_even_center_zero (f : ℂ → ℂ) (hf : ∀ z : ℂ, f (-z) = f z) (R : ℝ) :
    (∮ z in C(0,R), f z) = 0 := by
  have h := circleIntegral_even_neg_center f hf 0 R
  rw [neg_zero] at h
  linear_combination h/2

end NLS.ComplexAnalysis
