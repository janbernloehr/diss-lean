import NLS.FunctionalAnalysis.SquaredNeumann

/-!
# Squared Neumann inversion in an equivalent norm

Conjugation transports the geometric inverse back to the original Banach
space. Only the square in the equivalent norm needs to be small.
-/

noncomputable section
namespace NLS.SquaredNeumann
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The geometric inverse of `1-K²`, tested after a continuous change of coordinates. -/
def conjugateEvenCorrection (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K ^ 2)‖ < 1) : E →L[ℂ] E :=
  e.conjContinuousAlgEquiv.symm (evenCorrection (e.conjContinuousAlgEquiv K) (by simpa only [map_pow] using h))

/-- The transported inverse is the convergent geometric series in the original operator algebra. -/
theorem conjugateEvenCorrection_hasSum (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K ^ 2)‖ < 1) :
    HasSum (fun j : ℕ => (K ^ 2) ^ j) (conjugateEvenCorrection e K h) := by
  have hs := e.conjContinuousAlgEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum
    (evenCorrection_hasSum (e.conjContinuousAlgEquiv K) (by simpa only [map_pow] using h))
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousAlgEquiv.toContinuousLinearEquiv_apply,
    map_pow, ContinuousAlgEquiv.symm_apply_apply, conjugateEvenCorrection] using hs

/-- The inverse of `1-K` obtained from its conjugated small square. -/
def conjugateCorrection (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K ^ 2)‖ < 1) : E →L[ℂ] E :=
  e.conjContinuousAlgEquiv.symm (correction (e.conjContinuousAlgEquiv K) (by simpa only [map_pow] using h))

/-- The source's squared Neumann formula holds on the original space. -/
theorem conjugateCorrection_eq (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K ^ 2)‖ < 1) :
    conjugateCorrection e K h = (1 + K) * conjugateEvenCorrection e K h := by
  simp only [conjugateCorrection, conjugateEvenCorrection, correction, map_mul, map_add, map_one, ContinuousAlgEquiv.symm_apply_apply]

theorem conjugateEvenCorrection_mul (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K ^ 2)‖ < 1) :
    conjugateEvenCorrection e K h * (1 - K ^ 2) = 1 := by
  apply e.conjContinuousAlgEquiv.injective
  simpa only [ContinuousAlgEquiv.coe_toAlgEquiv, conjugateEvenCorrection, map_mul, map_sub, map_one, map_pow, ContinuousAlgEquiv.apply_symm_apply] using evenCorrection_mul (e.conjContinuousAlgEquiv K) (by simpa only [map_pow] using h)

theorem mul_conjugateEvenCorrection (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K ^ 2)‖ < 1) :
    (1 - K ^ 2) * conjugateEvenCorrection e K h = 1 := by
  apply e.conjContinuousAlgEquiv.injective
  simpa only [ContinuousAlgEquiv.coe_toAlgEquiv, conjugateEvenCorrection, map_mul, map_sub, map_one, map_pow, ContinuousAlgEquiv.apply_symm_apply] using mul_evenCorrection (e.conjContinuousAlgEquiv K) (by simpa only [map_pow] using h)

theorem conjugateCorrection_mul (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K ^ 2)‖ < 1) :
    conjugateCorrection e K h * (1 - K) = 1 := by
  apply e.conjContinuousAlgEquiv.injective
  simpa only [ContinuousAlgEquiv.coe_toAlgEquiv, conjugateCorrection, map_mul, map_sub, map_one, ContinuousAlgEquiv.apply_symm_apply] using correction_mul (e.conjContinuousAlgEquiv K) (by simpa only [map_pow] using h)

theorem mul_conjugateCorrection (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K ^ 2)‖ < 1) :
    (1 - K) * conjugateCorrection e K h = 1 := by
  apply e.conjContinuousAlgEquiv.injective
  simpa only [ContinuousAlgEquiv.coe_toAlgEquiv, conjugateCorrection, map_mul, map_sub, map_one, ContinuousAlgEquiv.apply_symm_apply] using mul_correction (e.conjContinuousAlgEquiv K) (by simpa only [map_pow] using h)

theorem conjugateCorrection_left (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K ^ 2)‖ < 1) (a : E) :
    conjugateCorrection e K h (a - K a) = a :=
  congrArg (fun T : E →L[ℂ] E => T a) (conjugateCorrection_mul e K h)

theorem conjugateCorrection_right (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K ^ 2)‖ < 1) (a : E) :
    conjugateCorrection e K h a - K (conjugateCorrection e K h a) = a :=
  congrArg (fun T : E →L[ℂ] E => T a) (mul_conjugateCorrection e K h)

theorem conjugateCorrection_unique (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K ^ 2)‖ < 1) (a b : E) (hab : a - K a = b) :
    a = conjugateCorrection e K h b := by
  rw [← hab, conjugateCorrection_left]

/-- The inverse commutes with the original operator. -/
theorem conjugateCorrection_commute (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K ^ 2)‖ < 1) (a : E) :
    K (conjugateCorrection e K h a) = conjugateCorrection e K h (K a) := by
  have hl := conjugateCorrection_left e K h a
  rw [map_sub] at hl
  exact sub_right_injective ((conjugateCorrection_right e K h a).trans hl.symm)

end NLS.SquaredNeumann
