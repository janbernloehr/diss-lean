import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Reality of circle integrals by reflection

Reflection of a real-centered circle reverses its orientation. If the
integrand is anti-conjugate at reflected points, these two signs
cancel and the circle integral is real.
-/

noncomputable section
open Set Complex ComplexConjugate
open scoped Real
namespace NLS.ComplexAnalysis

/-- A circle integral about a real center is real when its integrand
is anti-conjugate under reflection across the real axis. -/
theorem circleIntegral_im_eq_zero_of_anti_conj
    (f : ℂ → ℂ) (x R : ℝ) (hR : 0 < R)
    (hf : ∀ z ∈ Metric.sphere (x:ℂ) R, f (conj z) = -conj (f z)) :
    (∮ z in C((x:ℂ),R), f z).im = 0 := by
  let H : ℝ → ℂ := fun θ =>
    deriv (circleMap (x:ℂ) R) θ * f (circleMap (x:ℂ) R θ)
  have hneg (θ : ℝ) : H (-θ) = conj (H θ) := by
    have hz : circleMap (x:ℂ) R θ ∈ Metric.sphere (x:ℂ) R := by
      simp [abs_of_pos hR]
    have hx : conj (x:ℂ) = (x:ℂ) := by simp
    have hcircle : circleMap (x:ℂ) R (-θ) =
        conj (circleMap (x:ℂ) R θ) := by
      rw [conj_circleMap,hx]
    have hzero : circleMap 0 R (-θ) = conj (circleMap 0 R θ) :=
      (conj_circleMap_zero R θ).symm
    dsimp [H]
    simp only [deriv_circleMap,hcircle,hzero,hf _ hz,map_mul,Complex.conj_I]
    ring
  have hperiodic : Function.Periodic H (2*π) := by
    intro θ
    dsimp [H]
    simp only [deriv_circleMap]
    rw [periodic_circleMap 0 R θ,periodic_circleMap (x:ℂ) R θ]
  have hJ : (∫ θ in (0:ℝ)..2*π, H (-θ)) =
      ∫ θ in (0:ℝ)..2*π, H θ := by
    rw [intervalIntegral.integral_comp_neg H]
    simpa using (hperiodic.intervalIntegral_add_eq (-(2*π)) 0)
  have hconj : (∫ θ in (0:ℝ)..2*π, H (-θ)) =
      conj (∫ θ in (0:ℝ)..2*π, H θ) := by
    rw [show (fun θ : ℝ => H (-θ)) = (fun θ => conj (H θ)) from
      funext hneg]
    exact RCLike.conjLIE.toLinearIsometry.intervalIntegral_comp_comm H
  have hreal : conj (∫ θ in (0:ℝ)..2*π, H θ) =
      ∫ θ in (0:ℝ)..2*π, H θ := hconj.symm.trans hJ
  exact Complex.conj_eq_iff_im.mp hreal

end NLS.ComplexAnalysis
