import NLS.ZakharovShabat.SourceLemmaG3

/-! # The corrected weighted derivative bound in G.3

The estimate concerns M-E, uses the genuine Hermitian operator norm, and
holds uniformly on the exact original H1 source balls for every nonzero
complex spectral parameter and all times in the closed unit interval.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The full Hermitian remainder derivative is uniformly bounded after
exponential normalization, over every nonzero complex spectral parameter. -/
theorem classicalHermitianRemainder_derivative_weighted_sobolev_ball
    (M : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    Real.exp (-(|z.im| * t.val))*
      ‖deriv (classicalHermitianRemainderOperator (classicalSobolevPotential a) z) t‖ ≤
        4*((8+Real.pi)*M*Real.exp (4*M)) := by
  let E := Real.exp (-(|z.im| * t.val))
  let C := (8+Real.pi)*M*Real.exp (4*M)
  have hE : 0 < E := Real.exp_pos _
  have hd (v : ℂ × ℂ) :
      E*‖deriv (classicalSolutionRemainder (classicalSobolevPotential a) z v) t‖ ≤ C*‖v‖ := by
    have h := norm_deriv_classicalSolutionRemainder_sobolev_ball_le M a ha z hz v t
    dsimp only [C,E]
    nlinarith [h]
  rw [deriv_classicalHermitianRemainderOperator]
  have h₁ : ‖deriv (classicalSolutionRemainder (classicalSobolevPotential a) z (1,0)) t‖ ≤ C/E := by
    apply (le_div_iff₀ hE).mpr
    simpa [mul_comm] using hd (1,0)
  have h₂ : ‖deriv (classicalSolutionRemainder (classicalSobolevPotential a) z (0,1)) t‖ ≤ C/E := by
    apply (le_div_iff₀ hE).mpr
    simpa [mul_comm] using hd (0,1)
  have h := mul_le_mul_of_nonneg_left (norm_hermitianColumns_le _ _ (C/E) h₁ h₂) hE.le
  calc
    _ ≤ E*(4*(C/E)) := h
    _ = 4*C := by field_simp

/-- The corrected G.3 proof estimate on the exact original periodic H1 ball. -/
theorem sourceLemmaG3_weighted_remainder_derivative
    (M : ℝ) (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    Real.exp (-(|z.im| * t.val))*
      ‖deriv (classicalHermitianRemainderOperator (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) z) t‖ ≤
        4*((8+Real.pi)*(2*M)*Real.exp (4*(2*M))) :=
  classicalHermitianRemainder_derivative_weighted_sobolev_ball (2*M) _
    ((norm_sourceG3ClassicalCoefficients_le a).trans (by linarith)) z hz t

end NLS.ZakharovShabat
