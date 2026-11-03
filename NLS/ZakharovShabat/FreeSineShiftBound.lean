import NLS.ZakharovShabat.FreeSineExteriorBounds

/-! Bounded frequency perturbations preserve a uniform sine-ratio
bound on every separated spectral exterior. -/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖sin z‖ ≤ (Real.exp |z.im|) := by
  have he : ‖exp (-z*I)-exp (z*I)‖ = 2*‖sin z‖ := by
    have h := congrArg norm (Complex.two_sin (x := z))
    simpa only [norm_mul,norm_I,mul_one,norm_ofNat] using h.symm
  have ht := norm_sub_le (exp (-z*I)) (exp (z*I))
  rw [he] at ht
  simp only [norm_exp,mul_re,neg_re,neg_im,I_re,I_im,mul_zero,mul_one,zero_sub,neg_neg] at ht
  have h₁ := Real.exp_le_exp.mpr (le_abs_self z.im)
  have h₂ := Real.exp_le_exp.mpr (neg_le_abs z.im)
  linarith

theorem exists_bound_sin_ratio_of_separated_close {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, (∀ m : ℤ, r ≤ ‖z-(Real.pi:ℂ)*m‖) →
      ∀ w : ℂ, ‖w-z‖ ≤ 1 → ‖sin w/sin z‖ ≤ C := by
  obtain ⟨B,hB,hbound⟩ := exists_bound_exp_im_div_sin_of_separated hr
  refine ⟨B*Real.exp 1,mul_pos hB (Real.exp_pos _),?_⟩
  intro z hsep w hw
  have hs : 0 < ‖sin z‖ := norm_pos_iff.mpr
    (sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated hr hsep))
  have him : |w.im| ≤ |z.im|+1 := by
    have hd := (Complex.abs_im_le_norm (w-z)).trans hw
    calc
      |w.im| = |z.im+(w-z).im| := by congr 1; simp
      _ ≤ |z.im|+|(w-z).im| := abs_add_le _ _
      _ ≤ |z.im|+1 := by linarith
  have hn : ‖sin w‖ ≤ (Real.exp |z.im|)*Real.exp 1 :=
    (norm_sin_le_exp_abs_im w).trans (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr him)
  have hb : (Real.exp |z.im|)/‖sin z‖ ≤ B := by
    simpa only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hbound z hsep
  rw [norm_div]
  calc
    _ ≤ ((Real.exp |z.im|)*Real.exp 1)/‖sin z‖ := div_le_div_of_nonneg_right hn hs.le
    _ = ((Real.exp |z.im|)/‖sin z‖)*Real.exp 1 := by ring
    _ ≤ B*Real.exp 1 := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le

end NLS.ZakharovShabat
