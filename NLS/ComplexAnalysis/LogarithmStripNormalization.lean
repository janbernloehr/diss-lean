import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! # Fixing logarithmic phases by real interval barriers

A continuous real phase cannot leave an interval without meeting a
boundary. Imaginary integer multiples of pi are zeros of the hyperbolic
sine. Finally an exponential value determines a logarithm within a
closed strip of half-width pi about its prescribed value.
-/

noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem real_mem_Ioo_of_preconnected_avoids
    {X : Type*} [TopologicalSpace X] (f : X → ℝ) (S : Set X)
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (l u : ℝ)
    (hne : ∀ x ∈ S, f x ≠ l ∧ f x ≠ u)
    (a : X) (ha : a ∈ S) (hfa : f a ∈ Ioo l u) :
    ∀ x ∈ S, f x ∈ Ioo l u := by
  intro x hx
  constructor
  · by_contra h
    obtain ⟨b,hb,he⟩ := hS.intermediate_value hx ha hf
      (show l ∈ Icc (f x) (f a) from ⟨not_lt.mp h,hfa.1.le⟩)
    exact (hne b hb).1 he
  · by_contra h
    obtain ⟨b,hb,he⟩ := hS.intermediate_value ha hx hf
      (show u ∈ Icc (f a) (f x) from ⟨hfa.2.le,not_lt.mp h⟩)
    exact (hne b hb).2 he

theorem sinh_eq_zero_of_re_zero_im_int_pi (z : ℂ) (k : ℤ)
    (hre : z.re = 0) (him : z.im = (k : ℝ)*Real.pi) : sinh z = 0 := by
  have he : z = ((k : ℂ)*(Real.pi : ℂ))*I := by
    apply Complex.ext <;> simp [hre,him]
  rw [he,sinh_mul_I,Complex.sin_int_mul_pi,zero_mul]

theorem exp_neg_I_nat_pi (n : ℕ) :
    exp (-I*(n : ℂ)*Real.pi) = (-1 : ℂ)^n := by
  have he : -I*(n : ℂ)*Real.pi = (n : ℂ)*(-(Real.pi : ℂ)*I) := by ring
  rw [he,exp_nat_mul]
  simp

theorem eq_zero_of_exp_eq_one_of_abs_im_le_pi
    (z : ℂ) (he : exp z = 1) (him : |z.im| ≤ Real.pi) : z = 0 := by
  obtain ⟨k,hk⟩ := exp_eq_one_iff.mp he
  have hi := congrArg Complex.im hk
  simp only [mul_im,intCast_re,intCast_im,ofReal_re,ofReal_im,I_re,I_im,
    mul_re,mul_zero,zero_mul,sub_zero,add_zero,mul_one] at hi
  norm_num at hi
  have hklo : (-1 : ℝ) < k := by nlinarith [(abs_le.mp him).1,Real.pi_pos]
  have hkhi : (k : ℝ) < 1 := by nlinarith [(abs_le.mp him).2,Real.pi_pos]
  have hk0 : k = 0 := by
    have hkl : (-1 : ℤ) < k := by exact_mod_cast hklo
    have hku : k < (1 : ℤ) := by exact_mod_cast hkhi
    omega
  simpa only [hk0,Int.cast_zero,zero_mul] using hk

theorem eq_of_exp_eq_of_abs_im_sub_le_pi
    (z a : ℂ) (he : exp z = exp a) (him : |z.im-a.im| ≤ Real.pi) : z = a := by
  apply sub_eq_zero.mp
  apply eq_zero_of_exp_eq_one_of_abs_im_le_pi
  · rw [exp_sub,he,div_self (exp_ne_zero a)]
  · simpa only [sub_im] using him

end NLS.ComplexAnalysis
