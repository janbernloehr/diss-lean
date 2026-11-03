import NLS.Articles.KdVPseudomeasures.PeriodicProjectionConvergence

/-! The periodic part of source (33), for the ENTIRE original complex
endpoint space. Uniformity is on each FIXED original endpoint norm ball. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The source's original endpoint potentials have ACTUAL periodic projection
convergence to the literal free contour projector, uniformly on EACH fixed
original endpoint norm ball. The very SAME original H-minus-one distribution,
source circle, positive index and physical L2 normalization are retained. -/
theorem exists_uniform_sourceEndpointPeriodicProjection_sub_free_small
    (s : ℝ) (hs : AdmissiblePredualOrder s) (R : ℝ) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-s) ⊤, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) →
        ‖singularHillContinuousRieszProjection (sourceComplexHminusOne s hs q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularHillContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
        ‖singularHillLinfRieszProjection (sourceComplexHminusOne s hs q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularHillLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
        ‖singularHillL2RieszProjection (sourceComplexHminusOne s hs q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularHillL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon := by
  let r : ℝ := 3/4+s/2
  have hr : 0 ≤ r := by dsimp [r];linarith [hs.1]
  have hr1 : r < 1 := by dsimp [r];linarith [hs.2]
  have ht : 1 < ((-s)-(-r))*(2:ℝ≥0∞).toReal := by
    norm_num only [ENNReal.toReal_ofNat]
    dsimp [r]
    linarith [hs.2]
  let E : FourierLebesgueSpace (2:ℝ) (-s) ⊤ →L[ℂ] FourierLebesgueSpace (2:ℝ) (-r) 2 :=
    endpointLowerInclusion (-s) (-r) (by norm_num) ht
  have hsame (q : FourierLebesgueSpace (2:ℝ) (-s) ⊤) :
      hillSobolevBaseInclusion r hr1.le (E q) = sourceComplexHminusOne s hs q := by
    apply Subtype.ext
    rw [hillSobolevBaseInclusion_val,sourceComplexHminusOne_val]
    exact endpointLowerInclusion_val (-s) (-r) (by norm_num) ht q
  obtain ⟨N,hN,hbound⟩ := exists_uniform_sourcePeriodicProjection_sub_free_small r hr hr1 (‖E‖*R) heps
  refine ⟨N,hN,?_⟩
  intro q hq n hn
  have hEq : ‖E q‖ ≤ ‖E‖*R := (E.le_opNorm q).trans (mul_le_mul_of_nonneg_left hq (norm_nonneg E))
  have h := hbound (E q) hEq n hn
  rwa [hsame q] at h

end NLS.Articles.KdVPseudomeasures
