import NLS.Articles.KdVConvexity.PhysicalTaylorAtZero
import NLS.Articles.KdVConvexity.ActionHessianBounds
import NLS.Articles.KdVConvexity.LocalConsequences

/-! # Actual local inverse and uniform Hessian radius for physical KdV Hstar -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVConvexity.PhysicalHstarExtension

/-- The actual physical renormalized frequency map is analytically
invertible on genuine open neighborhoods of zero in positive-index ell2. -/
theorem local_gradient_inverse (E : PhysicalHstarExtension) :
    ∃ V W : Set ActionSpace, IsOpen V ∧ IsOpen W ∧ (0 : ActionSpace) ∈ V ∧
      (0 : ActionSpace) ∈ W ∧ V ⊆ E.domain ∧ actionGradient E.hamiltonian '' V=W ∧
      Set.BijOn (actionGradient E.hamiltonian) V W ∧
      ∃ G : ActionSpace → ActionSpace,
        AnalyticOnNhd ℂ (actionGradient E.hamiltonian) V ∧ AnalyticOnNhd ℂ G W ∧
        (∀ a ∈ V, G (actionGradient E.hamiltonian a)=a) ∧
        (∀ b ∈ W, G b ∈ V ∧ actionGradient E.hamiltonian (G b)=b) :=
  local_open_inverse_of_derivative_neg_six E.isOpen (analyticOnNhd_actionGradient _ E.analytic)
    (E.contains_cone zero_mem_positiveQuadrant) E.Taylor_at_zero.2.1 E.Taylor_at_zero.2.2

/-- One positive radius gives equation (1.8) for every complex action in
the ball and every real Hilbert direction, and strict concavity on the
positive ball. The normalization comes from the actual physical moments. -/
theorem local_hessian_bound_and_strict_concavity (E : PhysicalHstarExtension) :
    ∃ r : ℝ, 0<r ∧ ball (0 : ActionSpace) r ⊆ E.domain ∧
      (∀ a ∈ ball (0 : ActionSpace) r, ∀ v : ActionSpace, (∀ n : ℕ+, (v n).im=0) →
        (fderiv ℂ (fderiv ℂ E.hamiltonian) a v v).re ≤ -‖v‖^2) ∧
      StrictConcaveOn ℝ (ball (0 : ActionSpace) r ∩ positiveQuadrant)
        (fun a => (E.hamiltonian a).re) := by
  obtain ⟨r,hr,hball,hess⟩ := exists_action_ball_hessian_bound E.hamiltonian E.domain E.isOpen
    (E.contains_cone zero_mem_positiveQuadrant) E.analytic E.Taylor_at_zero.2.2
  exact ⟨r,hr,hball,hess,strictConcaveOn_action_positive_ball _ _ E.isOpen E.analytic r hball hess⟩

end NLS.Articles.KdVConvexity.PhysicalHstarExtension
