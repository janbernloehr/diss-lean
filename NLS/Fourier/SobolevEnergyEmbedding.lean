import NLS.Fourier.SobolevEnergy
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# An exact Hilbert-space model of the physical Sobolev norm

The function and its derivative form a pair of actual period-two `L²` functions.
The Euclidean product norm, scaled by `√2`, is exactly the unnormalized physical
`H¹` norm. This supplies a normed-space construction, rather than merely norm
inequalities, for the original interval domains.
-/

noncomputable section
namespace NLS.Fourier
open ZakharovShabat

/-- The physical function/derivative pair with the length-two normalization. -/
def sobolevEnergyEmbedding : ScalarDomain 2 →ₗ[ℂ] WithLp 2 (CircleL2 × CircleL2) where
  toFun a := (Real.sqrt 2 : ℂ) • WithLp.toLp 2
    (l2Synthesis (scalarInclusion a), sobolevDerivative a)
  map_add' a c := by
    simp only [map_add, ← Prod.mk_add_mk, WithLp.toLp_add, smul_add]
  map_smul' c a := by
    simp [← WithLp.toLp_smul, smul_comm]

theorem sobolevEnergyEmbedding_injective : Function.Injective sobolevEnergyEmbedding := by
  intro a c h
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)))
  have he := smul_right_injective (WithLp 2 (CircleL2 × CircleL2)) hs h
  apply scalarInclusion_injective
  apply l2Synthesis.injective
  exact congrArg (fun v : WithLp 2 (CircleL2 × CircleL2) => v.fst) he

/-- The Hilbert graph norm is exactly the physical Lebesgue Sobolev energy. -/
theorem norm_sq_sobolevEnergyEmbedding (a : ScalarDomain 2) :
    ‖sobolevEnergyEmbedding a‖ ^ 2 = intervalH1Energy
      (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) 0 2 := by
  change ‖(Real.sqrt 2 : ℂ) • WithLp.toLp 2
    (l2Synthesis (scalarInclusion a), sobolevDerivative a)‖ ^ 2 = _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), mul_pow, Real.sq_sqrt (by norm_num),
    WithLp.prod_norm_sq_eq_of_L2]
  change 2 * (‖l2Synthesis (scalarInclusion a)‖ ^ 2 + ‖l2Synthesis (derivative a)‖ ^ 2) = _
  rw [norm_l2Synthesis, norm_l2Synthesis, intervalH1Energy_sobolevSynthesis]

/-- Its norm, not only its square, is the ordinary physical `H¹` norm. -/
theorem norm_sobolevEnergyEmbedding (a : ScalarDomain 2) :
    ‖sobolevEnergyEmbedding a‖ = Real.sqrt (intervalH1Energy
      (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) 0 2) := by
  rw [← norm_sq_sobolevEnergyEmbedding, Real.sqrt_sq (norm_nonneg _)]

end NLS.Fourier
