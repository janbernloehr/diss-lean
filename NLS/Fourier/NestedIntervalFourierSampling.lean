import NLS.SequenceSpaces.WeightedCoordinateIntegral
import NLS.Fourier.PartialIntervalFourierSampling
import NLS.SequenceSpaces.Multiplier

/-! # Nested oscillatory L2 sampling

Bounded complex lattice displacements admit uniform nested sampling bounds using the inner L2 and outer L1 norms.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- The full reverse oscillatory phase preserves uniform partial-interval
L2 sampling at bounded complex lattice displacements. -/
theorem exists_reverse_partial_interval_lattice_coefficients
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (δ : NLS.Coeff ⊤) (t : Icc (0:ℝ) 1) :
    ∃ a : NLS.Coeff 2,
      (∀ n, a n = exp (2*I*((Real.pi:ℂ)*n+δ n)*t.val)*
        (∫ x in (0:ℝ)..t.val, f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x))) ∧
      ‖a‖ ≤ Real.exp (4*‖δ‖)*‖unitIntervalMemLpCoefficients f hf‖ := by
  obtain ⟨a,ha,han⟩ := exists_partial_interval_bounded_lattice_fourier_coefficients f hf δ t t.property
  let m (n : ℤ) := exp (2*I*((Real.pi:ℂ)*n+δ n)*t.val)
  have hm (n : ℤ) : ‖m n‖ ≤ Real.exp (2*‖δ‖) := by
    rw [show ‖m n‖ = Real.exp (2*I*((Real.pi:ℂ)*n+δ n)*t.val).re from norm_exp _]
    apply Real.exp_le_exp.mpr
    have he : (2*I*((Real.pi:ℂ)*n+δ n)*t.val).re = -2*((δ n).im*t.val) := by
      simp [Complex.mul_re,Complex.mul_im]
      ring
    rw [he]
    have ht : |(δ n).im*t.val| ≤ ‖δ‖ := by
      rw [abs_mul,abs_of_nonneg t.property.1]
      exact (mul_le_of_le_one_right (abs_nonneg _) t.property.2).trans
        ((Complex.abs_im_le_norm _).trans (lp.norm_apply_le_norm (by simp) δ n))
    nlinarith [neg_le_abs ((δ n).im*t.val)]
  let M : NLS.Coeff ⊤ := ⟨m,memℓp_infty ⟨Real.exp (2*‖δ‖),by rintro _ ⟨n,rfl⟩; exact hm n⟩⟩
  have hM : ‖M‖ ≤ Real.exp (2*‖δ‖) := lp.norm_le_of_forall_le (Real.exp_pos _).le hm
  refine ⟨Coeff.multiplier M a,?_,?_⟩
  · intro n
    rw [Coeff.multiplier_apply,ha n]
  · apply (Coeff.norm_multiplier_le M a).trans
    apply (mul_le_mul hM han (norm_nonneg _) (Real.exp_pos _).le).trans_eq
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring

/-- Nested oscillatory integrals retain an L2 sampling bound, using only
the inner density's L2 norm and the outer density's L1 norm. No extra
derivative or integration-by-parts estimate on either density is needed. -/
theorem exists_nested_interval_lattice_coefficients
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hf₂ : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (δ : NLS.Coeff ⊤) (t : Icc (0:ℝ) 1) :
    ∃ a : NLS.Coeff 2,
      (∀ n, a n = ∫ x in (0:ℝ)..t.val, g x*
        (exp (2*I*((Real.pi:ℂ)*n+δ n)*x)*
          (∫ y in (0:ℝ)..x, f y*exp (-2*I*((Real.pi:ℂ)*n+δ n)*y)))) ∧
      ‖a‖ ≤ (Real.exp (4*‖δ‖)*‖unitIntervalMemLpCoefficients f hf₂‖)*
        (∫ x in (0:ℝ)..1, ‖g x‖) := by
  let F (x : ℝ) (n : ℤ) := exp (2*I*((Real.pi:ℂ)*n+δ n)*x)*
    (∫ y in (0:ℝ)..x, f y*exp (-2*I*((Real.pi:ℂ)*n+δ n)*y))
  have hF (n : ℤ) : Continuous (fun x => F x n) := by
    have hi := (intervalIntegral.differentiable_integral_of_continuous (a := (0:ℝ))
      (show Continuous (fun y : ℝ => f y*exp (-2*I*((Real.pi:ℂ)*n+δ n)*y)) by fun_prop)).continuous
    exact (show Continuous (fun x : ℝ => exp (2*I*((Real.pi:ℂ)*n+δ n)*x)) by fun_prop).mul hi
  have hb (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      ∃ a : WeightedCoeff Weight.one 2, (∀ n, a.val n = F x n) ∧
        ‖a‖ ≤ Real.exp (4*‖δ‖)*‖unitIntervalMemLpCoefficients f hf₂‖ := by
    obtain ⟨a,ha,han⟩ := exists_reverse_partial_interval_lattice_coefficients f hf₂ δ ⟨x,hx⟩
    refine ⟨(WeightedCoeff.weightIsometry Weight.one 2).symm a,?_,?_⟩
    · intro n
      change a n/(Weight.one n:ℂ) = F x n
      simpa [F] using ha n
    · simpa only [LinearIsometryEquiv.norm_map] using han
  obtain ⟨a,ha,han⟩ := WeightedCoeff.exists_interval_integral_of_bounded_coordinates
    Weight.one F hF g hg _ (by positivity) hb t
  refine ⟨WeightedCoeff.weightEquiv Weight.one 2 a,?_,han⟩
  intro n
  simpa only [WeightedCoeff.weightEquiv_apply,Weight.one_apply,Complex.ofReal_one,one_mul] using ha n

end NLS.Fourier
