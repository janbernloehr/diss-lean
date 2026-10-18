import NLS.Fourier.BoundedLatticeMomentSeries
import NLS.Fourier.PiLatticeCoefficient
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual perturbed Fourier integrals as moment series

The scalar Taylor series sums to the physical Fourier integral for a continuous density on the unit interval. No matching endpoint values are required.
-/

noncomputable section
open Set Complex MeasureTheory
namespace NLS.Fourier

/-- The scalar Taylor-moment series sums to the actual perturbed Fourier
integral, with the original signed index and exact period-one normalization. -/
theorem hasSum_perturbed_lattice_moment_integrals
    (f : ℝ → ℂ) (hf : Continuous f) (n : ℤ) (δ : ℂ) :
    HasSum (fun k : ℕ => ((-2*I*δ)^k/(k.factorial:ℂ))*
      periodOneCoefficient (fun x => (x:ℂ)^k*f x) n)
      (∫ x in (0:ℝ)..1, f x*exp (-2*I*((Real.pi:ℂ)*n+δ)*x)) := by
  let μ := volume.restrict (Ioc (0:ℝ) 1)
  let F (k : ℕ) (x : ℝ) := ((-2*I*δ*x)^k/(k.factorial:ℂ))*
    (f x*exp (-2*I*((Real.pi:ℂ)*n)*x))
  have hF (k : ℕ) : Continuous (F k) := by dsimp [F]; fun_prop
  have hFi (k : ℕ) : Integrable (F k) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      ((hF k).intervalIntegrable 0 1)
  have hfi : Integrable f μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (hf.intervalIntegrable 0 1)
  have hbound (k : ℕ) : (∫ x, ‖F k x‖ ∂μ) ≤
      ((2*‖δ‖)^k/(k.factorial:ℝ))*(∫ x, ‖f x‖ ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hFi k).norm (hfi.norm.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hfree : ‖exp (-2*I*((Real.pi:ℂ)*n)*x)‖ = 1 := by
      simp [norm_exp,Complex.mul_re,Complex.mul_im]
    have hxnorm : ‖(x:ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx.1]
      exact hx.2
    dsimp only [F]
    simp only [norm_mul,norm_div,norm_pow,norm_neg,norm_ofNat,norm_I,
      mul_one,hfree,Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_of_le_one_right (by positivity) hxnorm) k
  have he : HasSum (fun k : ℕ => (2*‖δ‖)^k/(k.factorial:ℝ)) (Real.exp (2*‖δ‖)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hi := hasSum_integral_of_summable_integral_norm hFi
    (Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbound
      (he.summable.mul_right (∫ x, ‖f x‖ ∂μ)))
  have hpoint (x : ℝ) : (∑' k, F k x) = f x*exp (-2*I*((Real.pi:ℂ)*n+δ)*x) := by
    have hx : HasSum (fun k : ℕ => (-2*I*δ*x)^k/(k.factorial:ℂ)) (exp (-2*I*δ*x)) := by
      rw [Complex.exp_eq_exp_ℂ]
      exact NormedSpace.expSeries_div_hasSum_exp _
    have hh := (hx.mul_right (f x*exp (-2*I*((Real.pi:ℂ)*n)*x))).tsum_eq
    change (∑' k, F k x) = _ at hh
    rw [hh]
    rw [show -2*I*((Real.pi:ℂ)*n+δ)*(x:ℂ) =
      -2*I*((Real.pi:ℂ)*n)*x+(-2*I*δ*x) by ring,exp_add]
    ring
  have hterm (k : ℕ) : (∫ x, F k x ∂μ) = ((-2*I*δ)^k/(k.factorial:ℂ))*
      periodOneCoefficient (fun x => (x:ℂ)^k*f x) n := by
    change (∫ x in Ioc (0:ℝ) 1, F k x) = _
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      ← integral_pi_lattice_eq_periodOneCoefficient,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [F]
    rw [mul_pow]
    ring
  simpa only [hterm,hpoint,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using hi

end NLS.Fourier
