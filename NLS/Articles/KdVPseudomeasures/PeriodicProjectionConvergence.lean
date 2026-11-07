import NLS.KdV.HillPeriodicProjectionConvergence
import NLS.KdV.HillFreeRieszFourier
import NLS.Articles.KdVPseudomeasures.PeriodicNormalizedResolvent

/-! Actual periodic projection convergence and Appendix C.4(i) on the
original spaces and literal circles. We write t=-r, so |t|=r in the source
range 1/2<r<1. No estimate for the Dirichlet part C.4(ii) is asserted here. -/
noncomputable section
open Set Metric
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- ONE exact original Sobolev norm-ball cutoff gives the stronger one-log
periodic projection bound on ALL original physical L2 inputs, simultaneously
in continuous-output, essential-supremum and L2 operator norms. -/
theorem exists_uniform_sourcePeriodicProjection_log_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) 2, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) → 1 < Real.log (n:ℝ) ∧
        sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularHillResolventSet (hillSobolevBaseInclusion r hr1.le q) ∧
        ‖singularHillContinuousRieszProjection (hillSobolevBaseInclusion r hr1.le q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularHillContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ ≤
          hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖ ∧
        ‖singularHillLinfRieszProjection (hillSobolevBaseInclusion r hr1.le q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularHillLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ ≤
          hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖ ∧
        ‖singularHillL2RieszProjection (hillSobolevBaseInclusion r hr1.le q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularHillL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ ≤
          hillPeriodicProjectionConstant*Real.log (n:ℝ)*(n:ℝ)^(r-1)*‖q‖ := by
  obtain ⟨N,hN,hbound⟩ := exists_uniform_hillPeriodicProjection_log_bound r hr hr1 R
  refine ⟨N,hN,?_⟩
  intro q hq n hn
  have h := hbound (sobolevCoefficients (-r) 2 q) (by simpa only [LinearIsometryEquiv.norm_map] using hq) (n:ℕ) hn
  have he : hillSobolevBaseInclusion r hr1.le q = hillHalfPotentialBase r hr1.le (sobolevCoefficients (-r) 2 q) := rfl
  rw [he]
  simpa only [LinearIsometryEquiv.norm_map,freeHillValue_natCast_complex] using h

/-- The exact periodic Appendix C.4(i) squared-logarithm rate, with a
positive constant chosen BEFORE every original potential norm ball and ONE
cutoff before ALL complex potentials in that ball and ALL original indices.
The parameter convention t=-r covers the ENTIRE original -1<t<-1/2 range. -/
theorem sourcePeriodicProjection_appendixC4 (r : ℝ) (hr : 1/2 < r) (hr1 : r < 1) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ R : ℝ, ∀ Nmin : ℕ, ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) 2, ‖q‖ ≤ R →
        ∀ n : ℕ+, N ≤ (n:ℕ) →
          ‖singularHillLinfRieszProjection (hillSobolevBaseInclusion r hr1.le q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
            singularHillLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ ≤
            Ct*(Real.log (n:ℝ))^2/(n:ℝ)^(1-r)*‖q‖ := by
  refine ⟨hillPeriodicProjectionConstant,hillPeriodicProjectionConstant_pos,?_⟩
  intro R Nmin
  obtain ⟨N,hN,hbound⟩ := exists_uniform_sourcePeriodicProjection_log_bound r (by linarith) hr1 R
  refine ⟨max N Nmin,hN.trans (le_max_left _ _),le_max_right _ _,?_⟩
  intro q hq n hn
  obtain ⟨hlog,_,_,hI,_⟩ := hbound q hq n ((le_max_left N Nmin).trans hn)
  have hpow : (n:ℝ)^(r-1) = ((n:ℝ)^(1-r))⁻¹ := by
    rw [← Real.rpow_neg (by positivity : (0:ℝ) ≤ n),show -(1-r)=r-1 by ring]
  have hlog2 : Real.log (n:ℝ) ≤ (Real.log (n:ℝ))^2 := by nlinarith
  apply hI.trans
  calc
    _ ≤ hillPeriodicProjectionConstant*(Real.log (n:ℝ))^2*(n:ℝ)^(r-1)*‖q‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog2 hillPeriodicProjectionConstant_pos.le)
          (Real.rpow_nonneg (by positivity) _)) (norm_nonneg q)
    _ = _ := by rw [hpow];ring

/-- Genuine uniform periodic projection convergence on EVERY FIXED original
Sobolev ball in the full r<1 range, in all THREE source physical operator norms. -/
theorem exists_uniform_sourcePeriodicProjection_sub_free_small (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (R : ℝ) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) 2, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) →
        ‖singularHillContinuousRieszProjection (hillSobolevBaseInclusion r hr1.le q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularHillContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
        ‖singularHillLinfRieszProjection (hillSobolevBaseInclusion r hr1.le q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularHillLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
        ‖singularHillL2RieszProjection (hillSobolevBaseInclusion r hr1.le q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
          singularHillL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon := by
  obtain ⟨N,hN,hbound⟩ := exists_uniform_hillPeriodicProjection_sub_free_small r hr hr1 R heps
  refine ⟨N,hN,?_⟩
  intro q hq n hn
  have h := hbound (sobolevCoefficients (-r) 2 q) (by simpa only [LinearIsometryEquiv.norm_map] using hq) (n:ℕ) hn
  have he : hillSobolevBaseInclusion r hr1.le q = hillHalfPotentialBase r hr1.le (sobolevCoefficients (-r) 2 q) := rfl
  rw [he]
  simpa only [freeHillValue_natCast_complex] using h

end NLS.Articles.KdVPseudomeasures
