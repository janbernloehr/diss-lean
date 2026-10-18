import NLS.ZakharovShabat.SourceAngularBetaH1BallBound

/-! # Phase-error smoothing uniformly on physical H1 balls

The exact beta phase errors decay at inverse-bracket rate with constants
uniform on each physical H1 ball. Their multiplication operators gain
one sequence derivative at every real order and Banach exponent, including
infinity. The sequence weights are `(1+|n|)^r`. This concerns the phase
factor; it does not assert the full Birkhoff-minus-Fourier theorem.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- Beta and its real phase errors have inverse-bracket decay uniformly on physical H1 balls. -/
theorem beta_phase_uniform_physical_H1_ball (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ n : ℤ, (1+|(n:ℝ)|)*‖sourceAngularBetaCorrection (by simp) (by norm_num) n s
        (sobolevSourceInclusion a.val)‖ ≤ K ∧
        ∀ t : ℝ, (1+|(n:ℝ)|)*‖exp ((t:ℂ)*Complex.I*sourceAngularBetaCorrection (by simp) (by norm_num)
          n s (sobolevSourceInclusion a.val))-1‖ ≤ |t| *K := by
  obtain ⟨K,hK,hβ⟩ := D.betaCorrection_uniform_physical_H1_ball R
  refine ⟨K,hK,?_⟩
  intro a ha n
  refine ⟨hβ a ha n,fun t => ?_⟩
  have hphase := D.norm_betaPhase_sub_one_le ⟨sobolevSourceInclusion a.val,a.property⟩ n t
  calc
    _ ≤ (1+|(n:ℝ)|)*(|t| *‖sourceAngularBetaCorrection (by simp) (by norm_num) n s
      (sobolevSourceInclusion a.val)‖) := mul_le_mul_of_nonneg_left hphase (by positivity)
    _ = |t| *((1+|(n:ℝ)|)*‖sourceAngularBetaCorrection (by simp) (by norm_num) n s
      (sobolevSourceInclusion a.val)‖) := by ring
    _ ≤ |t| *K := mul_le_mul_of_nonneg_left (hβ a ha n) (abs_nonneg t)

/-- The exact phase-error multipliers gain a derivative uniformly on physical H1 balls. -/
theorem beta_phase_multipliers_uniform_physical_H1_ball (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ (p : ℝ≥0∞) (_ : Fact (1 ≤ p)) (r t : ℝ),
        ∃ T : WeightedCoeff (Weight.sobolev r) p →L[ℂ] WeightedCoeff (Weight.sobolev (r+1)) p,
          (∀ c n, (T c).val n = (exp ((t:ℂ)*Complex.I*sourceAngularBetaCorrection (by simp) (by norm_num)
            n s (sobolevSourceInclusion a.val))-1)*c.val n) ∧ ‖T‖ ≤ |t| *K := by
  obtain ⟨K,hK,h⟩ := D.beta_phase_uniform_physical_H1_ball R
  refine ⟨K,hK,?_⟩
  intro a ha p hp r t
  exact WeightedCoeff.exists_sobolev_gain_multiplier r _ (|t| *K) (by positivity)
    (fun n => (h a ha n).2 t)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
