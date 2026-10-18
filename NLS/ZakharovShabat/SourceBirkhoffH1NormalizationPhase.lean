import NLS.ZakharovShabat.SourceNormalizedActionRootH1Multiplier
import NLS.ZakharovShabat.SourceBirkhoffH1BallPhase

/-! # Smoothing of the combined Birkhoff normalization and phase

For the same original Birkhoff family, the actual normalization times
beta-phase error decays at inverse-bracket rate and its exact multiplier
gains one sequence derivative, uniformly on physical H1 balls. The full
Birkhoff-minus-Fourier result still requires spectral-coordinate estimates
and analyticity into the stronger target.
-/

noncomputable section
open Set Metric Complex MeasureTheory
open scoped ENNReal

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The actual normalization times beta phase has uniform inverse-bracket error on H1 balls. -/
theorem normalization_phase_uniform_physical_H1_ball (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ (n : ℤ) (t : ℝ), (1+|(n:ℝ)|)*
        ‖sourceNormalizedActionRoot (by simp) (by norm_num) n (sobolevSourceInclusion a.val)*
          exp ((t:ℂ)*Complex.I*sourceAngularBetaCorrection (by simp) (by norm_num)
            n s (sobolevSourceInclusion a.val))-1‖ ≤ (1+|t|)*K := by
  obtain ⟨A,hA,hroot⟩ := sourceNormalizedActionRoot_uniform_physical_H1_decay R
  obtain ⟨B,hB,hphase⟩ := D.beta_phase_uniform_physical_H1_ball R
  refine ⟨A+(1+A)*B,by positivity,?_⟩
  intro a ha n t
  let b : ℝ := 1+|(n:ℝ)|
  let ξ := sourceNormalizedActionRoot (by simp) (by norm_num) n (sobolevSourceInclusion a.val)
  let e := exp ((t:ℂ)*Complex.I*sourceAngularBetaCorrection (by simp) (by norm_num)
    n s (sobolevSourceInclusion a.val))
  have hb : 1 ≤ b := by dsimp only [b]; linarith [abs_nonneg (n:ℝ)]
  have hroot' : b^2*‖ξ-1‖ ≤ A := hroot a ha n
  have hlinear : b*‖ξ-1‖ ≤ A := by
    have hbb : b ≤ b^2 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hbb (norm_nonneg _)).trans hroot'
  have herr : ‖ξ-1‖ ≤ A := by
    calc
      _ = 1*‖ξ-1‖ := by rw [one_mul]
      _ ≤ b*‖ξ-1‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ ≤ A := hlinear
  have hξ : ‖ξ‖ ≤ 1+A := by
    have hn := norm_add_le (ξ-1) (1:ℂ)
    simp only [sub_add_cancel,norm_one] at hn
    linarith
  have he : b*‖e-1‖ ≤ |t| *B := (hphase a ha n).2 t
  have heq : ξ*e-1 = ξ*(e-1)+(ξ-1) := by ring
  change b*‖ξ*e-1‖ ≤ (1+|t|)*(A+(1+A)*B)
  rw [heq]
  calc
    _ ≤ b*(‖ξ‖*‖e-1‖+‖ξ-1‖) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [norm_mul] using norm_add_le (ξ*(e-1)) (ξ-1)) (by linarith)
    _ = ‖ξ‖*(b*‖e-1‖)+b*‖ξ-1‖ := by ring
    _ ≤ (1+A)*(|t| *B)+A := by
      exact add_le_add (mul_le_mul hξ he (by positivity) (by positivity)) hlinear
    _ ≤ (1+|t|)*(A+(1+A)*B) := by
      nlinarith [mul_nonneg (abs_nonneg t) hA, mul_nonneg (show 0 ≤ 1+A by positivity) hB]

/-- The exact normalization-phase error multiplier gains one derivative uniformly on H1 balls. -/
theorem normalization_phase_multipliers_uniform_physical_H1_ball (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ (q : ℝ≥0∞) (_ : Fact (1 ≤ q)) (r t : ℝ),
        ∃ T : WeightedCoeff (Weight.sobolev r) q →L[ℂ] WeightedCoeff (Weight.sobolev (r+1)) q,
          (∀ c n, (T c).val n =
            (sourceNormalizedActionRoot (by simp) (by norm_num) n (sobolevSourceInclusion a.val)*
              exp ((t:ℂ)*Complex.I*sourceAngularBetaCorrection (by simp) (by norm_num)
                n s (sobolevSourceInclusion a.val))-1)*c.val n) ∧ ‖T‖ ≤ (1+|t|)*K := by
  obtain ⟨K,hK,h⟩ := D.normalization_phase_uniform_physical_H1_ball R
  refine ⟨K,hK,?_⟩
  intro a ha q hq r t
  exact WeightedCoeff.exists_sobolev_gain_multiplier r _ ((1+|t|)*K) (by positivity)
    (fun n => h a ha n t)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
