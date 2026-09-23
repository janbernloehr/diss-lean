import NLS.ComplexAnalysis.HolomorphicCurveHomotopy
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circle paths and curve integrals

A counterclockwise circle parameterized on the unit interval defines a
closed path. Its complex one-form integral equals the usual circle integral
parameterized on `[0, 2π]`.
-/

noncomputable section
open Set Complex MeasureTheory Filter
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- The usual counterclockwise circle reparameterized on the unit interval. -/
def circlePath (c : ℂ) (R : ℝ) :
    Path (circleMap c R 0) (circleMap c R 0) :=
  Path.ofLine
    (f := fun t : ℝ => circleMap c R ((2 * Real.pi) * t))
    (by fun_prop)
    (by simp)
    (by simpa using (periodic_circleMap c R) 0)

private theorem deriv_scaled_circleMap (c : ℂ) (R t : ℝ) :
    deriv (fun x : ℝ => circleMap c R ((2 * Real.pi) * x)) t =
      (2 * Real.pi) • deriv (circleMap c R) ((2 * Real.pi) * t) := by
  have h := (hasDerivAt_circleMap c R ((2 * Real.pi) * t)).scomp t
    (hasDerivAt_const_mul (2 * Real.pi))
  simpa [Function.comp_def, deriv_circleMap, smul_eq_mul, mul_comm] using h.deriv

/-- The one-form integral around the unit-interval circle path agrees
with Mathlib's circle-integral parameterization. -/
theorem curveIntegral_circlePath (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (∫ᶜ z in circlePath c R, holomorphicOneForm f z) =
      ∮ z in C(c, R), f z := by
  let q : ℝ := 2 * Real.pi
  let g : ℝ → ℂ := fun θ => deriv (circleMap c R) θ * f (circleMap c R θ)
  have hpath (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      (circlePath c R).extend t = circleMap c R (q * t) := by
    rw [(circlePath c R).extend_apply
      (show t ∈ (Icc 0 1 : Set ℝ) from ⟨ht.1.le, ht.2.le⟩)]
    rfl
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      deriv (circlePath c R).extend t =
        q • deriv (circleMap c R) (q*t) := by
    have hEq : (circlePath c R).extend =ᶠ[nhds t]
        (fun x : ℝ => circleMap c R (q*x)) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun x hx => hpath x hx)
    rw [hEq.deriv_eq]
    exact deriv_scaled_circleMap c R t
  calc
    (∫ᶜ z in circlePath c R, holomorphicOneForm f z) =
        ∫ t in (0:ℝ)..1, q • g (q*t) := by
      rw [curveIntegral_eq_intervalIntegral_deriv]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      simp only [holomorphicOneForm_apply]
      rw [hpath t ht, hderiv t ht]
      dsimp [g]
      simp [mul_comm, mul_left_comm]
    _ = q • ∫ t in (0:ℝ)..1, g (q*t) := by
      rw [intervalIntegral.integral_smul]
    _ = ∫ θ in (0:ℝ)..q, g θ := by
      simpa only [mul_zero, mul_one] using
        (intervalIntegral.smul_integral_comp_mul_left
          (f := g) (a := 0) (b := 1) q)
    _ = ∮ z in C(c, R), f z := by
      simp [circleIntegral, q, g, smul_eq_mul, mul_comm]

end NLS.ComplexAnalysis
