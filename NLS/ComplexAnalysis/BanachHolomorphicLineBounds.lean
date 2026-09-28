import Mathlib.Analysis.Complex.Liouville

/-!
# Uniform Cauchy bounds along Banach-space lines

A holomorphic map bounded on a Banach ball has scalar-line Taylor
coefficients bounded uniformly over all directions in the unit ball.
The codomain may be any complex Banach space.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A bound on a Banach ball controls every derivative of every
complex line through its center, uniformly in unit directions. -/
theorem norm_iteratedDeriv_affineLine_le_of_ball_bound
    (f : E → F) (x : E) (r M : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball x (2*r)))
    (hb : ∀ y ∈ ball x (2*r), ‖f y‖ ≤ M)
    (v : E) (hv : ‖v‖ ≤ 1) (k : ℕ) :
    ‖iteratedDeriv k (fun z : ℂ => f (x+z • v)) 0‖ ≤
      k.factorial * M / r^k := by
  let g : ℂ → F := fun z => f (x+z • v)
  have hinside (z : ℂ) (hz : z ∈ closedBall 0 r) :
      x+z • v ∈ ball x (2*r) := by
    have hz' : ‖z‖ ≤ r := by
      simpa only [mem_closedBall, dist_zero_right] using hz
    have hv' : 0 ≤ ‖v‖ := norm_nonneg _
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
    have hmul : ‖z‖ * ‖v‖ ≤ r := by nlinarith
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul] using
      (show ‖z‖ * ‖v‖ < 2*r by linarith)
  have hdiff : DifferentiableOn ℂ g (closedBall 0 r) := by
    intro z hz
    have hzU : x+z • v ∈ ball x (2*r) := hinside z hz
    have hinner : DifferentiableAt ℂ (fun w : ℂ => x+w • v) z := by
      fun_prop
    exact (((hf _ hzU).differentiableAt
      (isOpen_ball.mem_nhds hzU)).comp z hinner).differentiableWithinAt
  have hdc : DiffContOnCl ℂ g (ball 0 r) :=
    (hdiff.mono closure_ball_subset_closedBall).diffContOnCl
  have hbound (z : ℂ) (hz : z ∈ sphere 0 r) : ‖g z‖ ≤ M :=
    hb _ (hinside z (sphere_subset_closedBall hz))
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    k hr hdc hbound

end NLS.ComplexAnalysis
