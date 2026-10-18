import NLS.Fourier.PiLatticeCoefficient
import Mathlib.Analysis.Complex.Exponential
import NLS.ComplexAnalysis.IntegralMajorantUnit

/-! # Fourier integrals at square-summably perturbed lattice points

An explicit Lipschitz estimate in the complex displacement preserves L2 summability of actual sampled Fourier integrals.
-/

noncomputable section
open Set Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Fourier

/-- An L1 density's actual sampled Fourier integral is Lipschitz in a
bounded complex displacement of the pi lattice, uniformly in the index. -/
theorem norm_perturbed_lattice_integral_sub_coefficient_le
    (f : ℝ → ℂ) (hf : Continuous f) (n : ℤ) (δ : ℂ) (D : ℝ) (hδ : ‖δ‖ ≤ D) :
    ‖(∫ x in (0:ℝ)..1, f x*exp (-2*I*((Real.pi:ℂ)*n+δ)*x))-periodOneCoefficient f n‖ ≤
      (2*Real.exp (2*D)*(∫ x in (0:ℝ)..1, ‖f x‖))*‖δ‖ := by
  have h1 : Continuous (fun x : ℝ => f x*exp (-2*I*((Real.pi:ℂ)*n+δ)*x)) := by fun_prop
  have h2 : Continuous (fun x : ℝ => f x*exp (-2*I*((Real.pi:ℂ)*n)*x)) := by fun_prop
  rw [← integral_pi_lattice_eq_periodOneCoefficient,
    ← intervalIntegral.integral_sub (h1.intervalIntegrable 0 1) (h2.intervalIntegrable 0 1)]
  have hpoint (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      ‖f x*exp (-2*I*((Real.pi:ℂ)*n+δ)*x)-f x*exp (-2*I*((Real.pi:ℂ)*n)*x)‖ ≤
        (2*Real.exp (2*D)*‖δ‖)*‖f x‖ := by
    let η : ℂ := -2*I*δ*x
    have hη : ‖η‖ ≤ 2*‖δ‖ := by
      simp only [η,norm_mul,norm_neg,norm_ofNat,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1]
      exact mul_le_of_le_one_right (by positivity) hx.2
    have he : ‖exp η-1‖ ≤ 2*‖δ‖*Real.exp (2*D) := by
      have hh := norm_exp_sub_sum_le_norm_mul_exp η 1
      simp only [Finset.sum_range_one,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,pow_one] at hh
      exact hh.trans (mul_le_mul hη (Real.exp_le_exp.mpr (hη.trans (by linarith))) (Real.exp_pos _).le (by positivity))
    have hfree : ‖exp (-2*I*((Real.pi:ℂ)*n)*x)‖ = 1 := by
      simp [norm_exp,Complex.mul_re,Complex.mul_im]
    have hid : f x*exp (-2*I*((Real.pi:ℂ)*n+δ)*x)-f x*exp (-2*I*((Real.pi:ℂ)*n)*x) =
        (f x*exp (-2*I*((Real.pi:ℂ)*n)*x))*(exp η-1) := by
      rw [show -2*I*((Real.pi:ℂ)*n+δ)*(x:ℂ) = -2*I*((Real.pi:ℂ)*n)*x+η by dsimp [η]; ring,exp_add]
      ring
    rw [hid,norm_mul,norm_mul,hfree,mul_one]
    exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (by ring)
  have hi := norm_integral_unit_le_mul_integral_norm _ (h1.sub h2) f hf
    (2*Real.exp (2*D)*‖δ‖) (by positivity) hpoint ⟨1,⟨zero_le_one,le_rfl⟩⟩
  exact hi.trans_eq (by ring)

/-- Square-summable spectral displacements preserve square-summability of
the actual sampled Fourier integrals, with a uniform norm estimate. -/
theorem exists_perturbed_lattice_coefficients
    (f : ℝ → ℂ) (hf : Continuous f) (c δ : NLS.Coeff 2)
    (hc : ∀ n, c n = periodOneCoefficient f n) (D : ℝ) (hδ : ‖δ‖ ≤ D) :
    ∃ a : NLS.Coeff 2,
      (∀ n, a n = ∫ x in (0:ℝ)..1, f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x)) ∧
      ‖a‖ ≤ ‖c‖+2*Real.exp (2*D)*(∫ x in (0:ℝ)..1, ‖f x‖)*‖δ‖ := by
  let L := ∫ x in (0:ℝ)..1, ‖f x‖
  let C := 2*Real.exp (2*D)*L
  have hL : 0 ≤ L := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let r (n : ℤ) := (∫ x in (0:ℝ)..1, f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x))-c n
  have hr (n : ℤ) : ‖r n‖ ≤ ‖((C:ℂ) • δ) n‖ := by
    have hh := norm_perturbed_lattice_integral_sub_coefficient_le f hf n (δ n) D
      ((lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) δ n).trans hδ)
    simpa only [r,hc,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hC,C,L] using hh
  let e : NLS.Coeff 2 := ⟨r,(lp.memℓp ((C:ℂ) • δ)).mono' hr⟩
  have he : ‖e‖ ≤ C*‖δ‖ := by
    have hh := lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) (fun n => show ‖e n‖ ≤ ‖((C:ℂ) • δ) n‖ from hr n)
    simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC] using hh
  refine ⟨c+e,?_,?_⟩
  · intro n
    change c n+((∫ x in (0:ℝ)..1, f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x))-c n) = _
    ring
  · exact (norm_add_le c e).trans (add_le_add le_rfl he)

end NLS.Fourier
