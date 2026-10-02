import NLS.ZakharovShabat.ClassicalSobolevPotential
import NLS.ZakharovShabat.ClassicalRemainderDerivativeBound

/-! # Fundamental-solution error estimates on H¹ balls

The regularity premises of the integration-by-parts argument are now
instantiated by Fourier synthesis. Constants depend only on the H¹
coefficient norm. This supplies the Sobolev uniformity needed in Appendix G.
-/

noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- Inverse-frequency decay for every H¹ potential, with no extra regularity premises. -/
theorem classicalNormalizedRemainder_sobolev_le
    (a : ScalarDomain 2 × ScalarDomain 2) (z : ℂ) (hz : z ≠ 0)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalNormalizedRemainder (classicalSobolevPotential a) z v t ≤
      (4+Real.pi)*‖a‖*‖v‖/‖z‖*Real.exp (4*‖a‖) := by
  obtain ⟨hf,hg,hfi,hgi⟩ := classicalSobolevPotential_regular a
  have h := classicalNormalizedRemainder_le_inverse_frequency
    (classicalSobolevPotential a) hf hg hfi hgi z hz v t
  have hb := classicalFirstBornUniformBudget_sobolev_le a
  have hn := norm_classicalSobolevPotential_le a
  calc
    _ ≤ classicalFirstBornUniformBudget (classicalSobolevPotential a)*‖v‖/(2*‖z‖)*
        Real.exp ‖classicalSobolevPotential a‖ := h
    _ ≤ ((8+2*Real.pi)*‖a‖)*‖v‖/(2*‖z‖)*Real.exp (4*‖a‖) := by
      gcongr
    _ = _ := by ring

/-- Time differentiation consumes the inverse-frequency factor and leaves an H¹-controlled bound. -/
theorem norm_deriv_classicalSolutionRemainder_sobolev_le
    (a : ScalarDomain 2 × ScalarDomain 2) (z : ℂ) (hz : z ≠ 0)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    Real.exp (-(|z.im| * t.val))*‖deriv (classicalSolutionRemainder (classicalSobolevPotential a) z v) t‖ ≤
      (8+Real.pi)*‖a‖*‖v‖*Real.exp (4*‖a‖) := by
  obtain ⟨hf,hg,hfi,hgi⟩ := classicalSobolevPotential_regular a
  have h := norm_deriv_classicalSolutionRemainder_weighted_le
    (classicalSobolevPotential a) hf hg hfi hgi z hz v t
  have hb := classicalFirstBornUniformBudget_sobolev_le a
  have hn := norm_classicalSobolevPotential_le a
  calc
    _ ≤ (classicalFirstBornUniformBudget (classicalSobolevPotential a)/2+
        ‖classicalSobolevPotential a‖)*‖v‖*Real.exp ‖classicalSobolevPotential a‖ := h
    _ ≤ (((8+2*Real.pi)*‖a‖)/2+4*‖a‖)*‖v‖*Real.exp (4*‖a‖) := by
      gcongr
    _ = _ := by ring

/-- The full error estimate is uniform on each H¹ ball. -/
theorem classicalNormalizedRemainder_sobolev_ball_le
    (M : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalNormalizedRemainder (classicalSobolevPotential a) z v t ≤
      (4+Real.pi)*M*‖v‖/‖z‖*Real.exp (4*M) := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  apply (classicalNormalizedRemainder_sobolev_le a z hz v t).trans
  gcongr

/-- The derivative estimate is likewise uniform on each H¹ ball. -/
theorem norm_deriv_classicalSolutionRemainder_sobolev_ball_le
    (M : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    Real.exp (-(|z.im| * t.val))*‖deriv (classicalSolutionRemainder (classicalSobolevPotential a) z v) t‖ ≤
      (8+Real.pi)*M*‖v‖*Real.exp (4*M) := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  apply (norm_deriv_classicalSolutionRemainder_sobolev_le a z hz v t).trans
  gcongr

private theorem remove_exponential_weight (b H r C : ℝ) (hb : b ≤ H) (hC : 0 ≤ C)
    (h : Real.exp (-b)*r ≤ C) : r ≤ Real.exp H*C := by
  calc
    r = Real.exp b*(Real.exp (-b)*r) := by
      rw [← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
    _ ≤ Real.exp b*C := mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    _ ≤ Real.exp H*C := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb) hC

/-- In a horizontal spectral strip the unweighted error decays uniformly on H¹ balls. -/
theorem norm_classicalSolutionRemainder_sobolev_strip_le
    (M H : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (hH : |z.im| ≤ H) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖classicalSolutionRemainder (classicalSobolevPotential a) z v t‖ ≤
      (4+Real.pi)*M*‖v‖/‖z‖*Real.exp (4*M+H) := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have h := remove_exponential_weight (|z.im| * t.val) H _ _
    (by nlinarith [abs_nonneg z.im,t.property.2]) (by positivity)
    (classicalNormalizedRemainder_sobolev_ball_le M a ha z hz v t)
  convert h using 1
  rw [mul_left_comm,← Real.exp_add,add_comm H]

/-- The unweighted time derivative stays bounded in a horizontal strip and on each H¹ ball. -/
theorem norm_deriv_classicalSolutionRemainder_sobolev_strip_le
    (M H : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (hH : |z.im| ≤ H) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖deriv (classicalSolutionRemainder (classicalSobolevPotential a) z v) t‖ ≤
      (8+Real.pi)*M*‖v‖*Real.exp (4*M+H) := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have h := remove_exponential_weight (|z.im| * t.val) H _ _
    (by nlinarith [abs_nonneg z.im,t.property.2]) (by positivity)
    (norm_deriv_classicalSolutionRemainder_sobolev_ball_le M a ha z hz v t)
  convert h using 1
  rw [mul_left_comm,← Real.exp_add,add_comm H]

end NLS.ZakharovShabat
