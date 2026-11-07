import NLS.FunctionalAnalysis.PeriodicContinuousCurveDerivative
import NLS.FunctionalAnalysis.PeriodicIntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Actual spatial and mixed derivatives of jointly smooth scalar fields.
Periodicity is inherited by differentiation in either variable. -/
noncomputable section
open scoped ContDiff
namespace NLS.FunctionalAnalysis

def spacePartial (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := fderiv ℝ f p (0, 1)

def timePartial (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := fderiv ℝ f p (1, 0)

theorem contDiff_spacePartial (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (spacePartial f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_timePartial (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (timePartial f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem hasDerivAt_spacePartial (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (t x : ℝ) :
    HasDerivAt (fun y => f (t, y)) (spacePartial f (t, x)) x := by
  exact (hf.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))

theorem hasDerivAt_timePartial (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (t x : ℝ) :
    HasDerivAt (fun s => f (s, x)) (timePartial f (t, x)) t := by
  exact (hf.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

theorem spacePartial_eq_deriv (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    (fun x => spacePartial f (t, x)) = deriv (fun x => f (t, x)) := by
  funext x
  exact (hasDerivAt_spacePartial f hf t x).deriv.symm

theorem periodic_spacePartial (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, Function.Periodic (fun x => f (t, x)) 1) (t : ℝ) :
    Function.Periodic (fun x => spacePartial f (t, x)) 1 := by
  rw [spacePartial_eq_deriv f hf]
  exact periodic_deriv _ 1 (hp t)

theorem periodic_timePartial (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, Function.Periodic (fun x => f (t, x)) 1) (t : ℝ) :
    Function.Periodic (fun x => timePartial f (t, x)) 1 := by
  intro x
  have he : (fun s => f (s, x + 1)) = (fun s => f (s, x)) := funext (fun s => hp s x)
  have h := hasDerivAt_timePartial f hf t (x + 1)
  rw [he] at h
  exact h.unique (hasDerivAt_timePartial f hf t x)

end NLS.FunctionalAnalysis
