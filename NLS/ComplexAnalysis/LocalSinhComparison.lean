import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

/-! # Recovering a small phase from its hyperbolic sine

Near zero, the complex hyperbolic sine has a uniform inverse Lipschitz
bound. At real zeros of cosine this also compares the oscillatory phases
in a discriminant formula.
-/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- A quantitative local inverse estimate, with no choice of an inverse branch. -/
theorem exists_norm_sub_le_two_mul_sinh_sub :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u v : ℂ, ‖u‖ < ε → ‖v‖ < ε →
      ‖u-v‖ ≤ 2*‖sinh u-sinh v‖ := by
  have hd : HasStrictDerivAt (fun z : ℂ => sinh z-z) 0 0 := by
    simpa using! (hasStrictDerivAt_sinh 0).sub (hasStrictDerivAt_id (0 : ℂ))
  obtain ⟨s,hs,hlip⟩ := hd.hasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt
    (1/2) (by norm_num)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨ε,hε,?_⟩
  intro u v hu hv
  have h := hlip.norm_sub_le (hball (by simpa using hu)) (hball (by simpa using hv))
  have he : u-v = (sinh u-sinh v)-((sinh u-u)-(sinh v-v)) := by abel
  have ht := norm_sub_le (sinh u-sinh v) ((sinh u-u)-(sinh v-v))
  rw [← he] at ht
  norm_num at h
  linarith

/-- At a real zero of cosine, the oscillatory factor has unit modulus. -/
theorem norm_cosh_shift_sub (r : ℝ) (hr : Real.cos r = 0) (u v : ℂ) :
    ‖cosh (-I*r+u)-cosh (-I*r+v)‖ = ‖sinh u-sinh v‖ := by
  have hc : cosh (-I*(r : ℂ)) = 0 := by
    rw [neg_mul,cosh_neg,mul_comm I,cosh_mul_I,← ofReal_cos,hr,ofReal_zero]
  have hs : ‖sinh (-I*(r : ℂ))‖ = 1 := by
    rw [neg_mul,sinh_neg,norm_neg,mul_comm I,sinh_mul_I,norm_mul,norm_I,mul_one,
      ← ofReal_sin,norm_real,Real.norm_eq_abs]
    have h := Real.sin_sq_add_cos_sq r
    rw [hr] at h
    nlinarith [sq_abs (Real.sin r),abs_nonneg (Real.sin r)]
  rw [cosh_add,cosh_add,hc,zero_mul,zero_mul,zero_add,zero_add,← mul_sub,norm_mul,hs,one_mul]

/-- Discriminant errors control small phase errors at every real zero of cosine. -/
theorem exists_norm_phase_sub_le_discriminant_error :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℝ) (u v : ℂ), Real.cos r = 0 →
      ‖u‖ < ε → ‖v‖ < ε →
      ‖u-v‖ ≤ ‖2*cosh (-I*r+u)-2*cosh (-I*r+v)‖ := by
  obtain ⟨ε,hε,hbound⟩ := exists_norm_sub_le_two_mul_sinh_sub
  refine ⟨ε,hε,?_⟩
  intro r u v hr hu hv
  rw [← mul_sub,norm_mul,norm_ofNat,norm_cosh_shift_sub r hr]
  exact hbound u v hu hv

end NLS.ComplexAnalysis
