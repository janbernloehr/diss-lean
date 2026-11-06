import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.Ring

/-! Reflection of actual circle integrals. A negative radius is a rotation
of the parameter, so spectral negation preserves orientation and contributes
the derivative factor minus one. No analyticity hypothesis is required. -/
noncomputable section
open Set Complex Real
namespace NLS.ComplexAnalysis

theorem circleIntegral_neg_radius (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (∮ z in C(c,-R), f z) = ∮ z in C(c,R), f z := by
  let g : ℝ → ℂ := fun θ => deriv (circleMap c R) θ*f (circleMap c R θ)
  have hg : Function.Periodic g (2*Real.pi) := by
    intro θ
    dsimp only [g]
    rw [deriv_circleMap,deriv_circleMap,periodic_circleMap,periodic_circleMap]
  have he : (∮ z in C(c,-R), f z) = ∫ θ in (0:ℝ)..2*Real.pi, g (θ+Real.pi) := by
    unfold circleIntegral
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [g,deriv_circleMap,circleMap_neg_radius,smul_eq_mul]
  rw [he,intervalIntegral.integral_comp_add_right]
  simpa only [zero_add,add_comm (2*Real.pi) Real.pi,circleIntegral,smul_eq_mul,g] using
    hg.intervalIntegral_add_eq Real.pi 0

/-- Pullback under z -> -z, including its exact derivative and orientation. -/
theorem circleIntegral_neg_pullback (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (∮ z in C(c,R), -f (-z)) = ∮ z in C(-c,R), f z := by
  have hm (d : ℂ) (θ : ℝ) : circleMap (-d) (-R) θ = -circleMap d R θ := by
    simp only [circleMap,ofReal_neg]
    ring
  have hd (θ : ℝ) : deriv (circleMap (-c) (-R)) θ = -deriv (circleMap c R) θ := by
    rw [deriv_circleMap,deriv_circleMap]
    have h := hm 0 θ
    simp only [neg_zero] at h
    rw [h]
    ring
  rw [← circleIntegral_neg_radius f (-c) R]
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [smul_eq_mul,hm,hd]
  ring

end NLS.ComplexAnalysis
