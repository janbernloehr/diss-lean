import NLS.Articles.KdVConvexity.PhysicalTaylorAtZero
import NLS.Articles.KdVConvexity.ActionHessianBounds
import NLS.ComplexAnalysis.AnalyticQuadraticRemainder

/-! # The full Hilbert quadratic expansion of physical KdV Hstar -/
noncomputable section
set_option autoImplicit false
open Filter Topology Asymptotics
namespace NLS.Articles.KdVConvexity.PhysicalHstarExtension

theorem differential_at_zero (E : PhysicalHstarExtension) : fderiv ℂ E.hamiltonian 0=0 := by
  ext v
  rw [fderiv_eq_tsum_actionGradient,E.Taylor_at_zero.2.1]
  simp

theorem hessian_at_zero (E : PhysicalHstarExtension) (v w : ActionSpace) :
    fderiv ℂ (fderiv ℂ E.hamiltonian) 0 v w=(-6 : ℂ)*actionBilinearPairing v w := by
  rw [action_hessian_eq_pairing_gradient_derivative E.hamiltonian 0
    (E.analytic 0 (E.contains_cone zero_mem_positiveQuadrant)),E.Taylor_at_zero.2.2]
  simp only [actionBilinearPairing,smul_apply,ContinuousLinearMap.id_apply,map_smul,
    smul_eq_mul]

/-- The physical remainder is cubic in the full Hilbert norm, with
unconjugated action squares and the actual coefficient minus three. -/
theorem quadratic_Taylor_remainder (E : PhysicalHstarExtension) :
    (fun a : ActionSpace => E.hamiltonian a+3*actionBilinearPairing a a)
      =O[𝓝 0] (fun a => ‖a‖^3) := by
  have h := NLS.ComplexAnalysis.analytic_quadratic_remainder E.hamiltonian
    (E.analytic 0 (E.contains_cone zero_mem_positiveQuadrant))
  apply h.congr_left
  intro a
  rw [E.Taylor_at_zero.1,E.differential_at_zero,E.hessian_at_zero]
  simp only [zero_apply,sub_zero]
  ring

theorem quadratic_Taylor_remainder_raw_actions (E : PhysicalHstarExtension) :
    (fun a : ActionSpace => E.hamiltonian a+3*∑' n : ℕ+, (a n)^2)
      =O[𝓝 0] (fun a => ‖a‖^3) := by
  simpa only [actionBilinearPairing_eq_tsum,pow_two] using E.quadratic_Taylor_remainder

end NLS.Articles.KdVConvexity.PhysicalHstarExtension
