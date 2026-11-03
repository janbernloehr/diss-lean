import NLS.KdV.HillFreePeriodSequence
import NLS.ComplexAnalysis.AnalyticUnitDerivativeInverse

/-! The assembled nonlinear l2-valued free Hill period map has the
ACTUAL full Banach derivative equal to the identity. Strict
differentiability and the same inverse of norm one work for every n. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

theorem fderiv_hillFreePeriodEquation_zero (n : ℕ+) :
    fderiv ℂ (hillFreePeriodEquation n) 0 = hillFreePeriodJacobianOperator := by
  have hd := (analyticAt_hillFreePeriodEquation n 0).differentiableAt.hasFDerivAt
  apply ContinuousLinearMap.ext
  intro h
  ext m
  let ev := lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m
  have hc := ev.hasFDerivAt.comp 0 hd
  have he : ev ∘ hillFreePeriodEquation n = hillFreePeriodEquationRow n m (hillFreePeriodCircle m) := by
    funext d
    rfl
  rw [he] at hc
  have hf := hc.fderiv
  rw [hillFreePeriodEquationRow_fderiv_eq_eval] at hf
  have hv := congrArg (fun L : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] ℂ => L h) hf
  exact hv.symm

theorem hasFDerivAt_hillFreePeriodEquation_zero (n : ℕ+) :
    HasFDerivAt (hillFreePeriodEquation n) hillFreePeriodJacobianOperator 0 := by
  simpa only [fderiv_hillFreePeriodEquation_zero] using
    (analyticAt_hillFreePeriodEquation n 0).differentiableAt.hasFDerivAt

theorem hasStrictFDerivAt_hillFreePeriodEquation_zero (n : ℕ+) :
    HasStrictFDerivAt (hillFreePeriodEquation n) hillFreePeriodJacobianOperator 0 := by
  simpa only [fderiv_hillFreePeriodEquation_zero] using
    (analyticAt_hillFreePeriodEquation n 0).hasStrictFDerivAt

theorem norm_fderiv_hillFreePeriodEquation_zero (n : ℕ+) :
    ‖fderiv ℂ (hillFreePeriodEquation n) 0‖ = 1 := by
  rw [fderiv_hillFreePeriodEquation_zero,norm_hillFreePeriodJacobianOperator]

theorem isUnit_fderiv_hillFreePeriodEquation_zero (n : ℕ+) :
    IsUnit (fderiv ℂ (hillFreePeriodEquation n) 0) := by
  rw [fderiv_hillFreePeriodEquation_zero]
  exact isUnit_one

theorem exists_hillFreePeriodEquation_localInverse (n : ℕ+) :
    ∃ G : lp (fun _ : ℕ+ => ℂ) 2 → lp (fun _ : ℕ+ => ℂ) 2,
      AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      (∀ᶠ d in nhds (0:lp (fun _ : ℕ+ => ℂ) 2), G (hillFreePeriodEquation n d) = d) ∧
      (∀ᶠ e in nhds (0:lp (fun _ : ℕ+ => ℂ) 2), hillFreePeriodEquation n (G e) = e) ∧
      fderiv ℂ G 0 = hillFreePeriodJacobianOperator := by
  have h := NLS.ComplexAnalysis.exists_localInverse_of_isUnit_fderiv
    (analyticAt_hillFreePeriodEquation n 0) (isUnit_fderiv_hillFreePeriodEquation_zero n)
  have hi : Ring.inverse hillFreePeriodJacobianOperator = hillFreePeriodJacobianOperator :=
    Ring.inverse_one (lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
  simpa only [hillFreePeriodEquation_zero,fderiv_hillFreePeriodEquation_zero,hi] using h

end NLS.KdV
