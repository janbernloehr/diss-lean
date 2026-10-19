import NLS.Fourier.NestedIntervalFourierSampling
import NLS.Fourier.PartialIntervalOscillatorySampling

/-! # Sampling both diagonal oscillatory terms

Boundary and nested integrals admit a common l2 realization at bounded complex lattice displacements.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- The boundary and nested oscillatory pieces of the diagonal response
admit a common l2 realization at bounded complex lattice displacements. -/
theorem exists_diagonal_oscillatory_lattice_coefficients
    (r g : ℝ → ℂ) (hr : Continuous r) (hg : Continuous g)
    (hr₂ : MemLp r 2 (volume.restrict (Ioc 0 1)))
    (c : ℂ) (δ : NLS.Coeff ⊤) (t : Icc (0:ℝ) 1) :
    ∃ q : NLS.Coeff 2,
      (∀ n, q n = c*exp (I*((Real.pi:ℂ)*n+δ n)*t.val)*
        (∫ x in (0:ℝ)..t.val, r x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x))-
        exp (-I*((Real.pi:ℂ)*n+δ n)*t.val)*(∫ x in (0:ℝ)..t.val, g x*
          (exp (2*I*((Real.pi:ℂ)*n+δ n)*x)*
            (∫ y in (0:ℝ)..x, r y*exp (-2*I*((Real.pi:ℂ)*n+δ n)*y))))) ∧
      ‖q‖ ≤ (‖c‖*Real.exp (3*‖δ‖)+Real.exp (5*‖δ‖)*(∫ x in (0:ℝ)..1, ‖g x‖))*
        ‖unitIntervalMemLpCoefficients r hr₂‖ := by
  obtain ⟨u,hu,hun⟩ := exists_partial_interval_oscillatory_lattice_coefficients r hr₂ δ t t.property
  obtain ⟨v,hv,hvn⟩ := exists_nested_interval_lattice_coefficients r g hr hg hr₂ δ t
  let m (n : ℤ) := exp (-I*((Real.pi:ℂ)*n+δ n)*t.val)
  have hm (n : ℤ) : ‖m n‖ ≤ Real.exp ‖δ‖ := by
    rw [show ‖m n‖ = Real.exp (-I*((Real.pi:ℂ)*n+δ n)*t.val).re from norm_exp _]
    apply Real.exp_le_exp.mpr
    have he : (-I*((Real.pi:ℂ)*n+δ n)*t.val).re = (δ n).im*t.val := by simp [Complex.mul_re]
    rw [he]
    apply (le_abs_self _).trans
    rw [abs_mul,abs_of_nonneg t.property.1]
    exact (mul_le_of_le_one_right (abs_nonneg _) t.property.2).trans
      ((Complex.abs_im_le_norm _).trans (lp.norm_apply_le_norm (by simp) δ n))
  let M : NLS.Coeff ⊤ := ⟨m,memℓp_infty ⟨Real.exp ‖δ‖,by rintro _ ⟨n,rfl⟩; exact hm n⟩⟩
  have hM : ‖M‖ ≤ Real.exp ‖δ‖ := lp.norm_le_of_forall_le (Real.exp_pos _).le hm
  refine ⟨c • u-Coeff.multiplier M v,?_,?_⟩
  · intro n
    change c*u n-Coeff.multiplier M v n = _
    rw [Coeff.multiplier_apply,hu n,hv n]
    dsimp only [M,m]
    ring
  · have hi : 0 ≤ ∫ x in (0:ℝ)..1, ‖g x‖ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)
    calc
      _ ≤ ‖c • u‖+‖Coeff.multiplier M v‖ := norm_sub_le _ _
      _ ≤ ‖c‖*‖u‖+‖M‖*‖v‖ := by rw [norm_smul]; exact add_le_add le_rfl (Coeff.norm_multiplier_le M v)
      _ ≤ ‖c‖*(Real.exp (3*‖δ‖)*‖unitIntervalMemLpCoefficients r hr₂‖)+
          Real.exp ‖δ‖*((Real.exp (4*‖δ‖)*‖unitIntervalMemLpCoefficients r hr₂‖)*
            (∫ x in (0:ℝ)..1, ‖g x‖)) :=
        add_le_add (mul_le_mul_of_nonneg_left hun (norm_nonneg _))
          (mul_le_mul hM hvn (norm_nonneg _) (Real.exp_pos _).le)
      _ = _ := by
        have he : Real.exp ‖δ‖*Real.exp (4*‖δ‖) = Real.exp (5*‖δ‖) := by rw [← Real.exp_add]; congr 1; ring
        linear_combination (∫ x in (0:ℝ)..1, ‖g x‖)*‖unitIntervalMemLpCoefficients r hr₂‖*he

end NLS.Fourier
