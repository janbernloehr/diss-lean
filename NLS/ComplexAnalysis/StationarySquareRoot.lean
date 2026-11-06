import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.LinearCombination

/-! # Stationarity from a genuine local square identity -/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- A differentiable nonzero local square root is stationary in every
direction in which its actual square is stationary. -/
theorem fderiv_apply_eq_zero_of_eventually_sq
    (R F : A → ℂ) (a v : A) (hR : DifferentiableAt ℂ R a) (hne : R a≠0)
    (hsq : ∀ᶠ p in 𝓝 a, R p^2=F p) (hz : (fderiv ℂ F a) v=0) :
    (fderiv ℂ R a) v=0 := by
  have heq : (fun p => R p*R p) =ᶠ[𝓝 a] F := by
    filter_upwards [hsq] with p hp
    simpa only [pow_two] using hp
  have hd := congrArg (fun L : A →L[ℂ] ℂ => L v) heq.fderiv_eq
  have hm := (hR.hasFDerivAt.mul hR.hasFDerivAt).fderiv
  change fderiv ℂ (fun p => R p*R p) a=_ at hm
  rw [hm] at hd
  change R a*((fderiv ℂ R a) v)+R a*((fderiv ℂ R a) v)=(fderiv ℂ F a) v at hd
  rw [hz] at hd
  have hprod : R a*((fderiv ℂ R a) v)=0 := by linear_combination hd/2
  exact (mul_eq_zero.mp hprod).resolve_left hne

end NLS.ComplexAnalysis
