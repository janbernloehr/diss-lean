import NLS.Fourier.PartialIntervalFourierSampling
import NLS.SequenceSpaces.Multiplier

/-! # Partial-interval sampling with the free propagator

The free oscillatory propagator preserves the L2 sampling estimate uniformly over the physical period.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- The free propagator preserves the partial-interval sampling bound,
with a uniform exponential constant over the whole physical period. -/
theorem exists_partial_interval_oscillatory_lattice_coefficients
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (δ : NLS.Coeff ⊤) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ a : NLS.Coeff 2,
      (∀ n, a n = exp (I*((Real.pi:ℂ)*n+δ n)*t)*
        (∫ x in (0:ℝ)..t, f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x))) ∧
      ‖a‖ ≤ Real.exp (3*‖δ‖)*‖unitIntervalMemLpCoefficients f hf‖ := by
  obtain ⟨a,ha,hn⟩ := exists_partial_interval_bounded_lattice_fourier_coefficients f hf δ t ht
  have hm (n : ℤ) : ‖exp (I*((Real.pi:ℂ)*n+δ n)*t)‖ ≤ Real.exp ‖δ‖ := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    have hr : (I*((Real.pi:ℂ)*n+δ n)*(t:ℂ)).re = -((δ n).im*t) := by
      simp [Complex.mul_re,Complex.mul_im]
    rw [hr]
    apply (neg_le_abs _).trans
    rw [abs_mul,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_right (abs_nonneg _) ht.2).trans
      ((Complex.abs_im_le_norm _).trans (lp.norm_apply_le_norm (by simp) δ n))
  let m : NLS.Coeff ⊤ := ⟨fun n => exp (I*((Real.pi:ℂ)*n+δ n)*t),
    memℓp_infty ⟨Real.exp ‖δ‖,by rintro _ ⟨n,rfl⟩; exact hm n⟩⟩
  have hmn : ‖m‖ ≤ Real.exp ‖δ‖ := lp.norm_le_of_forall_le (Real.exp_pos _).le hm
  refine ⟨Coeff.multiplier m a,?_,?_⟩
  · intro n
    rw [Coeff.multiplier_apply,ha n]
  · apply (Coeff.norm_multiplier_le m a).trans
    apply (mul_le_mul hmn hn (norm_nonneg _) (Real.exp_pos _).le).trans_eq
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring

end NLS.Fourier
