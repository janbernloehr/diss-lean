import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open ComplexOrder
open scoped ComplexConjugate ENNReal

namespace NLS.ComplexAnalysis

theorem complex_sqrt_real_formula (x : ℝ) :
    Complex.sqrt (x : ℂ)=(Real.sqrt x : ℂ)+I*(Real.sqrt (-x) : ℂ) := by
  by_cases hx : 0≤x
  · rw [Complex.sqrt_of_nonneg (by exact_mod_cast hx)]
    simp only [Complex.ofReal_re,Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr hx),Complex.ofReal_zero,mul_zero,add_zero]
  · have hx' : x≤0 := (lt_of_not_ge hx).le
    have hn : (0 : ℂ)≤((-x : ℝ) : ℂ) := by exact_mod_cast neg_nonneg.mpr hx'
    have he : (x : ℂ)= -((-x : ℝ) : ℂ) := by simp
    rw [he,Complex.sqrt_neg_of_nonneg hn,Complex.sqrt_of_nonneg hn]
    simp only [Complex.ofReal_re,Real.sqrt_eq_zero_of_nonpos hx',Complex.ofReal_zero,zero_add]

theorem continuous_complex_sqrt_real : Continuous (fun x : ℝ => Complex.sqrt (x : ℂ)) := by
  have he : (fun x : ℝ => Complex.sqrt (x : ℂ))=
      (fun x : ℝ => (Real.sqrt x : ℂ)+I*(Real.sqrt (-x) : ℂ)) := funext complex_sqrt_real_formula
  rw [he]
  fun_prop

end NLS.ComplexAnalysis
