import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Unit-modulus roots of the unimodular monodromy polynomial

This is an algebraic prerequisite for whole-line Floquet theory. It does
not identify an unbounded operator's spectrum or its spectral measures.
-/
noncomputable section
set_option autoImplicit false
open Complex ComplexConjugate
namespace NLS.ZakharovShabat

/-- A real unimodular quadratic has a unit-modulus root exactly when its
trace lies in the closed interval from minus two to two. -/
theorem exists_unit_root_floquet_quadratic_iff (d : ℝ) :
    (∃ μ : ℂ, ‖μ‖ = 1 ∧ μ^2-(d : ℂ)*μ+1 = 0) ↔ |d| ≤ 2 := by
  constructor
  · rintro ⟨μ,hμ,hpoly⟩
    have hunit : μ * conj μ = 1 := by rw [Complex.mul_conj',hμ]; norm_num
    have hd : (d : ℂ) = μ+conj μ := by
      linear_combination -conj μ * hpoly + (μ-(d : ℂ)) * hunit
    have hre : d = 2*μ.re := by
      have h := congrArg Complex.re hd
      simpa only [Complex.ofReal_re,Complex.add_re,Complex.conj_re,two_mul] using h
    have hb := Complex.abs_re_le_norm μ
    rw [hμ] at hb
    rw [hre,abs_mul]
    norm_num
    linarith
  · intro hd
    have hs : 0 ≤ 1-(d/2)^2 := by
      obtain ⟨hl,hu⟩ := abs_le.mp hd
      nlinarith
    let μ : ℂ := ⟨d/2,Real.sqrt (1-(d/2)^2)⟩
    have hsq := Real.sq_sqrt hs
    refine ⟨μ,?_,?_⟩
    · have hn : ‖μ‖^2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq]
        simp only [Complex.normSq_apply,μ]
        nlinarith
      nlinarith [norm_nonneg μ]
    · simp only [pow_two] at hsq
      apply Complex.ext <;>
        simp only [pow_two,Complex.add_re,Complex.add_im,Complex.sub_re,
          Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
          Complex.ofReal_im,Complex.one_re,Complex.one_im,Complex.zero_re,
          Complex.zero_im,μ] <;> nlinarith

/-- The characteristic determinant of any two-by-two unimodular matrix. -/
theorem det_sub_smul_one_eq_floquet_quadratic
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1) (μ : ℂ) :
    (M-μ • 1).det = μ^2-M.trace*μ+1 := by
  rw [← hM]
  simp only [Matrix.det_fin_two,Matrix.trace,Fin.sum_univ_two,
    Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  norm_num
  ring

/-- A real-trace unimodular monodromy has a unit-modulus characteristic
root exactly at the trace levels in the closed interval `[-2,2]`. -/
theorem exists_unit_characteristic_root_iff
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1)
    (hreal : M.trace.im = 0) :
    (∃ μ : ℂ, ‖μ‖ = 1 ∧ (M-μ • 1).det = 0) ↔ |M.trace.re| ≤ 2 := by
  have he : (M.trace.re : ℂ) = M.trace := Complex.ext rfl hreal.symm
  simp_rw [det_sub_smul_one_eq_floquet_quadratic M hM]
  simpa only [he] using exists_unit_root_floquet_quadratic_iff M.trace.re

end NLS.ZakharovShabat
