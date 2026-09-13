import NLS.ComplexAnalysis.BanachHolomorphicLimit
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Local uniform analytic approximation and smoothness

The approximation hypothesis uses uniform convergence on an actual open ball.
Schwarz estimates preserve this hypothesis under Fréchet differentiation, so
iteration gives continuous complex derivatives of every finite order.
-/

noncomputable section
open Filter Topology Metric
open scoped ContDiff
universe u
namespace NLS.ComplexAnalysis
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Around every point, the approximants converge uniformly and are eventually analytic on a common ball. -/
def HasLocalUniformAnalyticApproximation (u : ℕ → E → F) (f : E → F) : Prop :=
  ∀ x : E, ∃ r : ℝ, 0 < r ∧ TendstoUniformlyOn u f atTop (ball x (2*r)) ∧
    ∀ᶠ n in atTop, AnalyticOnNhd ℂ (u n) (ball x (2*r))

/-- Local uniform analytic approximation gives complex Fréchet differentiability. -/
theorem HasLocalUniformAnalyticApproximation.differentiable {u : ℕ → E → F} {f : E → F}
    (h : HasLocalUniformAnalyticApproximation u f) : Differentiable ℂ f := by
  intro x
  obtain ⟨r,hr,hf,hu⟩ := h x
  have hd := (tendstoUniformlyOn_fderiv_ball u f x r hr (hu.mono (fun _ hn => hn.differentiableOn)) hf).1
  exact (hd x (mem_ball_self hr)).differentiableAt (ball_mem_nhds x hr)

/-- The derivatives converge in operator norm on a neighborhood of every point. -/
theorem HasLocalUniformAnalyticApproximation.uniform_fderiv {u : ℕ → E → F} {f : E → F}
    (h : HasLocalUniformAnalyticApproximation u f) (x : E) :
    ∃ r : ℝ, 0 < r ∧ TendstoUniformlyOn (fun n => fderiv ℂ (u n)) (fderiv ℂ f) atTop (ball x r) := by
  obtain ⟨r,hr,hf,hu⟩ := h x
  exact ⟨r,hr,(tendstoUniformlyOn_fderiv_ball u f x r hr
    (hu.mono (fun _ hn => hn.differentiableOn)) hf).2⟩

/-- Uniform analytic approximation is preserved under Fréchet differentiation. -/
theorem HasLocalUniformAnalyticApproximation.fderiv {u : ℕ → E → F} {f : E → F}
    (h : HasLocalUniformAnalyticApproximation u f) :
    HasLocalUniformAnalyticApproximation (fun n => fderiv ℂ (u n)) (fderiv ℂ f) := by
  intro x
  obtain ⟨r,hr,hf,hu⟩ := h x
  refine ⟨r/2,half_pos hr,?_,?_⟩
  · rw [show 2*(r/2) = r by ring]
    exact
      (tendstoUniformlyOn_fderiv_ball u f x r hr (hu.mono (fun _ hn => hn.differentiableOn)) hf).2
  · filter_upwards [hu] with n hn
    apply hn.fderiv.mono
    apply ball_subset_ball
    linarith

/-- All finite complex Fréchet derivatives of the limit exist and are continuous. -/
theorem HasLocalUniformAnalyticApproximation.contDiff_nat (n : ℕ) {u : ℕ → E → F} {f : E → F}
    (h : HasLocalUniformAnalyticApproximation u f) : ContDiff ℂ n f := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr h.differentiable.continuous
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    exact ⟨h.differentiable,by simp,ih h.fderiv⟩

/-- The uniform limit is smooth over the complex field, including on infinite-dimensional domains. -/
theorem HasLocalUniformAnalyticApproximation.contDiff {u : ℕ → E → F} {f : E → F}
    (h : HasLocalUniformAnalyticApproximation u f) : ContDiff ℂ ∞ f :=
  contDiff_infty.mpr (fun n => h.contDiff_nat n)

end NLS.ComplexAnalysis
