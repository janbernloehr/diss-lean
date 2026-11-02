import NLS.SequenceSpaces.BoundedCoordinateDifferentiable
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! # The identity derivative from coordinate quadratic germs

Banach differentiability is required first. Coordinate identities then
identify its actual bounded derivative, without inferring norm
convergence from coordinatewise limits.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem fderiv_eq_id_of_coordinate_quadratic_germs (F : Coeff p → Coeff p)
    (hF : DifferentiableAt ℂ F 0)
    (hcoord : ∀ j : ℤ, ∃ c : ℂ, (fun x => F x j) =ᶠ[𝓝 0] (fun x => x j+c*(x j)^2)) :
    fderiv ℂ F 0 = ContinuousLinearMap.id ℂ (Coeff p) := by
  apply ContinuousLinearMap.ext
  intro x
  ext j
  rw [fderiv_apply_of_differentiableAt F 0 x j hF]
  obtain ⟨c,hc⟩ := hcoord j
  let e : Coeff p →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) p j
  have he : HasFDerivAt (fun y : Coeff p => y j) e 0 := e.hasFDerivAt
  have hpoly : HasFDerivAt (fun y : Coeff p => y j+c*(y j)^2) e 0 := by
    apply (he.add ((he.pow 2).const_mul c)).congr_fderiv
    ext y
    simp [e]
  rw [(hpoly.congr_of_eventuallyEq hc).fderiv]
  rfl

end NLS.Coeff
