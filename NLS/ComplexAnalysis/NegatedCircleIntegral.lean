import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! # Change of variable by negation on a circle

Negation preserves orientation and negates the differential. A half-turn
of the periodic circle parameter proves the literal integral identity.
-/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem circleMap_add_pi_neg_center (c : ℂ) (R θ : ℝ) :
    circleMap (-c) R (θ+Real.pi) = -circleMap c R θ := by
  simp only [circleMap,ofReal_add,add_mul,exp_add,exp_pi_mul_I]
  ring

theorem circleIntegral_comp_neg (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (∮ z in C(c,R), f (-z)) = -(∮ z in C(-c,R), f z) := by
  let G : ℝ → ℂ := fun θ => deriv (circleMap (-c) R) θ * f (circleMap (-c) R θ)
  have hperiodic : Function.Periodic G (2*Real.pi) := by
    intro θ
    dsimp [G]
    simp only [deriv_circleMap]
    rw [periodic_circleMap 0 R θ,periodic_circleMap (-c) R θ]
  have hshift (θ : ℝ) :
      G (θ+Real.pi) = -(deriv (circleMap c R) θ * f (-circleMap c R θ)) := by
    dsimp [G]
    simp only [deriv_circleMap,circleMap_add_pi_neg_center]
    have hzero := circleMap_add_pi_neg_center 0 R θ
    simp only [neg_zero] at hzero
    rw [hzero]
    ring
  have hI : (∫ θ in (0 : ℝ)..2*Real.pi, G (θ+Real.pi)) =
      ∫ θ in (0 : ℝ)..2*Real.pi, G θ := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add,add_comm Real.pi] using hperiodic.intervalIntegral_add_eq Real.pi 0
  have he : (fun θ : ℝ => G (θ+Real.pi)) =
      fun θ => -(deriv (circleMap c R) θ * f (-circleMap c R θ)) := funext hshift
  rw [he,intervalIntegral.integral_neg] at hI
  change _ = -_
  change (∫ θ in (0 : ℝ)..2*Real.pi, deriv (circleMap c R) θ * f (-circleMap c R θ)) = -_
  exact neg_eq_iff_eq_neg.mp hI

end NLS.ComplexAnalysis
