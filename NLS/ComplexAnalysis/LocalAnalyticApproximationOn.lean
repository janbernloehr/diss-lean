import NLS.ComplexAnalysis.LocalAnalyticApproximation

/-!
# Local uniform analytic approximation on an open Banach domain

Uniform convergence on a fixed ball around each point of an open domain
survives Fréchet differentiation on a smaller ball. Iteration gives
complex smoothness of the limit on that domain, including in infinite
dimensional Banach spaces.
-/

noncomputable section
open Filter Topology Metric
open scoped ContDiff
universe u
namespace NLS.ComplexAnalysis
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A common open domain with uniform analytic approximation on an
actual ball around each of its points. -/
def HasLocalUniformAnalyticApproximationOn
    (u : ℕ → E → F) (f : E → F) (S : Set E) : Prop :=
  IsOpen S ∧
    ∀ x ∈ S, ∃ r : ℝ, 0 < r ∧ ball x (2*r) ⊆ S ∧
      TendstoUniformlyOn u f atTop (ball x (2*r)) ∧
      ∀ᶠ n in atTop, AnalyticOnNhd ℂ (u n) (ball x (2*r))

/-- Open-domain analyticity of the approximants and uniform convergence
on a fixed neighborhood at every point yield the ball-based criterion. -/
theorem HasLocalUniformAnalyticApproximationOn.of_open_local_uniform
    {u : ℕ → E → F} {f : E → F} {S : Set E}
    (hSopen : IsOpen S)
    (hanalytic : ∀ n : ℕ, AnalyticOnNhd ℂ (u n) S)
    (huniform : ∀ x ∈ S, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      TendstoUniformlyOn u f atTop U) :
    HasLocalUniformAnalyticApproximationOn u f S := by
  refine ⟨hSopen, ?_⟩
  intro x hx
  obtain ⟨U, hUopen, hxU, hconv⟩ := huniform x hx
  obtain ⟨R, hR, hball⟩ :=
    Metric.mem_nhds_iff.mp ((hUopen.inter hSopen).mem_nhds ⟨hxU, hx⟩)
  refine ⟨R/2, half_pos hR, ?_, ?_, ?_⟩
  · rw [show 2*(R/2) = R by ring]
    exact (fun y hy => (hball hy).2)
  · rw [show 2*(R/2) = R by ring]
    exact hconv.mono (fun y hy => (hball hy).1)
  · exact Eventually.of_forall (fun n => (hanalytic n).mono (by
      intro y hy
      have hyR : y ∈ ball x R := by simpa only [show 2*(R/2) = R by ring] using hy
      exact (hball hyR).2))

variable [CompleteSpace F]

/-- The limit is complex differentiable throughout the open domain. -/
theorem HasLocalUniformAnalyticApproximationOn.differentiableOn
    {u : ℕ → E → F} {f : E → F} {S : Set E}
    (h : HasLocalUniformAnalyticApproximationOn u f S) :
    DifferentiableOn ℂ f S := by
  intro x hx
  obtain ⟨r, hr, _, hconv, hanalytic⟩ := h.2 x hx
  have hd := (tendstoUniformlyOn_fderiv_ball u f x r hr
    (hanalytic.mono (fun _ hn => hn.differentiableOn)) hconv).1
  exact (hd x (mem_ball_self hr)).differentiableAt
    (ball_mem_nhds x hr) |>.differentiableWithinAt

/-- Uniform convergence of the full Fréchet derivatives on a smaller
ball around every point of the domain. -/
theorem HasLocalUniformAnalyticApproximationOn.uniform_fderiv
    {u : ℕ → E → F} {f : E → F} {S : Set E}
    (h : HasLocalUniformAnalyticApproximationOn u f S) (x : E) (hx : x ∈ S) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ S ∧
      TendstoUniformlyOn (fun n => fderiv ℂ (u n)) (fderiv ℂ f)
        atTop (ball x r) := by
  obtain ⟨r, hr, hsub, hconv, hanalytic⟩ := h.2 x hx
  refine ⟨r, hr, ?_, (tendstoUniformlyOn_fderiv_ball u f x r hr
    (hanalytic.mono (fun _ hn => hn.differentiableOn)) hconv).2⟩
  exact (ball_subset_ball (by linarith)).trans hsub

/-- The open-domain uniform approximation property is preserved by
Fréchet differentiation. -/
theorem HasLocalUniformAnalyticApproximationOn.fderiv
    {u : ℕ → E → F} {f : E → F} {S : Set E}
    (h : HasLocalUniformAnalyticApproximationOn u f S) :
    HasLocalUniformAnalyticApproximationOn
      (fun n => fderiv ℂ (u n)) (fderiv ℂ f) S := by
  refine ⟨h.1, ?_⟩
  intro x hx
  obtain ⟨r, hr, hsub, hconv, hanalytic⟩ := h.2 x hx
  refine ⟨r/2, half_pos hr, ?_, ?_, ?_⟩
  · rw [show 2*(r/2) = r by ring]
    exact (ball_subset_ball (by linarith)).trans hsub
  · rw [show 2*(r/2) = r by ring]
    exact (tendstoUniformlyOn_fderiv_ball u f x r hr
      (hanalytic.mono (fun _ hn => hn.differentiableOn)) hconv).2
  · filter_upwards [hanalytic] with n hn
    apply hn.fderiv.mono
    apply ball_subset_ball
    linarith

/-- Every finite complex differentiability order holds on the domain. -/
theorem HasLocalUniformAnalyticApproximationOn.contDiffOn_nat
    (n : ℕ) {u : ℕ → E → F} {f : E → F} {S : Set E}
    (h : HasLocalUniformAnalyticApproximationOn u f S) :
    ContDiffOn ℂ n f S := by
  induction n generalizing F with
  | zero => exact contDiffOn_zero.mpr h.differentiableOn.continuousOn
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen h.1]
    exact ⟨h.differentiableOn, by simp, ih h.fderiv⟩

/-- The open-domain limit is complex smooth, with uniform derivative
convergence on a ball at every point. -/
theorem HasLocalUniformAnalyticApproximationOn.contDiffOn
    {u : ℕ → E → F} {f : E → F} {S : Set E}
    (h : HasLocalUniformAnalyticApproximationOn u f S) :
    ContDiffOn ℂ ∞ f S :=
  contDiffOn_infty.mpr (fun n => h.contDiffOn_nat n)

end NLS.ComplexAnalysis
