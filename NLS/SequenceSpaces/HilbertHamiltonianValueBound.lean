import NLS.SequenceSpaces.HilbertScalarConcavity
import Mathlib.Analysis.Complex.RealDeriv
import NLS.ComplexAnalysis.SecondDerivativeQuadraticBound

/-! # A local value bound for an analytic Hilbert action Hamiltonian -/
noncomputable section
open Set Metric Complex
namespace NLS.Coeff

/-- The quantitative Hessian bound implies a quadratic bound on every real radial segment. -/
theorem real_value_le_negative_half_norm_sq
    (H : Coeff 2 → ℂ) (V : Set (Coeff 2)) (hH : AnalyticOnNhd ℂ H V)
    (hzero : H 0 = 0) (hdzero : scalarGradient H 0 = 0)
    (r : ℝ) (hball : ball (0:Coeff 2) r ⊆ V)
    (hess : ∀ b ∈ ball (0:Coeff 2) r, ∀ J : RealCoeff 2,
      (fderiv ℂ (fderiv ℂ H) b (RealCoeff.complexCLM 2 J) (RealCoeff.complexCLM 2 J)).re ≤ -‖J‖^2)
    (J : RealCoeff 2) (hJ : ‖J‖ < r) :
    (H (RealCoeff.complexCLM 2 J)).re ≤ -‖J‖^2/2 := by
  let j := RealCoeff.complexCLM 2 J
  let f := fun t : ℝ => (H ((t:ℂ) • j)).re
  let f₁ := fun t : ℝ => (fderiv ℂ H ((t:ℂ) • j) j).re
  let f₂ := fun t : ℝ => (fderiv ℂ (fderiv ℂ H) ((t:ℂ) • j) j j).re
  have hmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : (t:ℂ) • j ∈ ball (0:Coeff 2) r := by
    rw [mem_ball_zero_iff,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg j)).trans_lt (by simpa [j,norm_real_hilbert_inclusion] using hJ)
  have hline (z : ℂ) : HasDerivAt (fun w : ℂ => w • j) j z := by
    simpa only [one_smul,id_eq] using! (hasDerivAt_id z).smul_const j
  have hf (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt f (f₁ t) t := by
    have h := ((hH _ (hball (hmem t ht))).differentiableAt.hasFDerivAt.comp_hasDerivAt (t:ℂ) (hline t)).comp_ofReal
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  have hf₁ (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt f₁ (f₂ t) t := by
    have h := ((hH.fderiv _ (hball (hmem t ht))).differentiableAt.hasFDerivAt.comp_hasDerivAt (t:ℂ) (hline t))
    have he := (h.clm_apply (hasDerivAt_const (t:ℂ) j)).comp_ofReal
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t he
    simpa only [ContinuousLinearMap.map_zero,add_zero] using! hre
  have hfzero : f 0 = 0 := by simp only [f,ofReal_zero,zero_smul,hzero,zero_re]
  have hf₁zero : f₁ 0 = 0 := by
    simp only [f₁,ofReal_zero,zero_smul,fderiv_eq_dualPairing_scalarGradient,hdzero,map_zero,zero_apply,zero_re]
  have hb := NLS.ComplexAnalysis.quadratic_upper_of_second_derivative f f₁ f₂ (‖J‖^2) hf hf₁
    (fun t ht => hess _ (hmem t ht) J) hfzero hf₁zero
  simpa only [f,ofReal_one,one_smul] using hb

end NLS.Coeff
