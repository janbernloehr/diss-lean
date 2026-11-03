import NLS.ComplexAnalysis.ParametricSineSquareCosineMean
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem cosine_first_moment_eq_sine_square_deriv
    (g : ℂ → ℂ) (τ δ : ℂ) (U : Set ℂ) (hg : AnalyticOnNhd ℂ g U)
    (hsegment : ∀ θ ∈ Icc (0 : ℝ) Real.pi, τ+δ*(Real.cos θ : ℂ) ∈ U) :
    (∫ θ in (0 : ℝ)..Real.pi, (Real.cos θ : ℂ)*g (τ+δ*(Real.cos θ : ℂ))) =
      δ*(∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*deriv g (τ+δ*(Real.cos θ : ℂ))) := by
  let Z : ℂ → ℂ := fun θ => τ+δ*Complex.cos θ
  have hz (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) : Z (θ : ℂ) ∈ U := by
    simpa only [Z,← Complex.ofReal_cos] using hsegment θ hθ
  have hG : ContinuousOn (fun θ : ℝ => g (Z (θ : ℂ))) (Icc (0 : ℝ) Real.pi) :=
    hg.continuousOn.comp (by dsimp [Z];fun_prop) hz
  have hG' : ContinuousOn (fun θ : ℝ => deriv g (Z (θ : ℂ))) (Icc (0 : ℝ) Real.pi) :=
    hg.deriv.continuousOn.comp (by dsimp [Z];fun_prop) hz
  have hcos : Continuous (fun θ : ℝ => (Real.cos θ : ℂ)) := continuous_ofReal.comp Real.continuous_cos
  have hsin : Continuous (fun θ : ℝ => (Real.sin θ : ℂ)) := continuous_ofReal.comp Real.continuous_sin
  have hA : IntervalIntegrable (fun θ : ℝ => (Real.cos θ : ℂ)*g (Z (θ : ℂ))) volume 0 Real.pi :=
    (hcos.continuousOn.mul hG).intervalIntegrable_of_Icc Real.pi_pos.le
  have hB : IntervalIntegrable (fun θ : ℝ => (Real.sin θ : ℂ)^2*deriv g (Z (θ : ℂ))) volume 0 Real.pi :=
    ((hsin.pow 2).continuousOn.mul hG').intervalIntegrable_of_Icc Real.pi_pos.le
  have hd (θ : ℂ) (hθ : Z θ ∈ U) :
      HasDerivAt (fun e : ℂ => Complex.sin e*g (Z e))
        (Complex.cos θ*g (Z θ)-δ*((Complex.sin θ)^2*deriv g (Z θ))) θ := by
    have hZ : HasDerivAt Z (δ*(-Complex.sin θ)) θ :=
      ((Complex.hasDerivAt_cos θ).const_mul δ).const_add τ
    have h := (Complex.hasDerivAt_sin θ).mul ((hg _ hθ).differentiableAt.hasDerivAt.comp θ hZ)
    convert h using 1 <;> first | rfl | (simp only [Function.comp_apply]; ring)
  have hdr (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
      HasDerivAt (fun e : ℝ => (Real.sin e : ℂ)*g (Z (e : ℂ)))
        ((Real.cos θ : ℂ)*g (Z (θ : ℂ))-δ*((Real.sin θ : ℂ)^2*deriv g (Z (θ : ℂ)))) θ := by
    simpa only [← Complex.ofReal_sin,← Complex.ofReal_cos] using (hd (θ : ℂ) (hz θ hθ)).comp_ofReal
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le
    (hsin.continuousOn.mul hG)
    (fun θ hθ => hdr θ (Ioo_subset_Icc_self hθ))
    (hA.sub (hB.const_mul δ))
  rw [intervalIntegral.integral_sub hA (hB.const_mul δ),intervalIntegral.integral_const_mul] at hi
  simp only [Pi.mul_apply,Real.sin_zero,Real.sin_pi,ofReal_zero,zero_mul,sub_zero] at hi
  simpa only [Z,← Complex.ofReal_cos] using sub_eq_zero.mp hi

variable {A : Type}

theorem parametricSineSquareCosineMean_zero (g : ℂ × A → ℂ) (t : A → ℂ) (a : A) :
    parametricSineSquareCosineMean g t (0,a) = (Real.pi : ℂ)/2*g (t a,a) := by
  simp only [parametricSineSquareCosineMean,zero_mul,add_zero]
  rw [intervalIntegral.integral_mul_const]
  have hi : (∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2) = (Real.pi : ℂ)/2 := by
    simp only [← ofReal_pow,intervalIntegral.integral_ofReal,integral_sin_sq,
      Real.sin_zero,Real.sin_pi,zero_mul,sub_zero,zero_add,ofReal_div,ofReal_ofNat]
  rw [hi]

end NLS.ComplexAnalysis
