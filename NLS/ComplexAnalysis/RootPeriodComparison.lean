import NLS.ComplexAnalysis.HolomorphicCircleIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Comparing two normalized root periods

The cancellation identity is equation (38) in arXiv:1606.07052v1.
It retains both zero periods; no complex mean-value assertion is used.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis

/-- Comparing the psi and critical-root zero periods isolates a quadratic remainder. -/
theorem root_comparison_period_identity
    (sigma rho nu c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (w zeta chi : ℂ → ℂ)
    (hw : ContinuousOn w (sphere c R)) (hzeta : ContinuousOn zeta (sphere c R))
    (hchi : ContinuousOn chi (sphere c R))
    (hw0 : ∀ z ∈ sphere c R, w z ≠ 0)
    (hnu : ∀ z ∈ sphere c R, nu-z ≠ 0)
    (hpsi : (∮ z in C(c,R), ((sigma-z)/w z)*(zeta z/(nu-z))) = 0)
    (hcritical : (∮ z in C(c,R), ((rho-z)/w z)*chi z) = 0) :
    (sigma-rho)*(∮ z in C(c,R), ((nu-rho)/(nu-z))*zeta z/w z) =
      (∮ z in C(c,R), (z-rho)*(zeta z-chi z)/w z) +
      (∮ z in C(c,R), (z-rho)^2*zeta z/((nu-z)*w z)) := by
  let P := fun z => ((sigma-z)/w z)*(zeta z/(nu-z))
  let C := fun z => ((rho-z)/w z)*chi z
  let E := fun z => (z-rho)*(zeta z-chi z)/w z
  let Q := fun z => (z-rho)^2*zeta z/((nu-z)*w z)
  let N := fun z => ((nu-rho)/(nu-z))*zeta z/w z
  have hden : ContinuousOn (fun z => nu-z) (sphere c R) := continuousOn_const.sub continuousOn_id
  have hP : CircleIntegrable P c R :=
    (((continuousOn_const.sub continuousOn_id).div hw hw0).mul (hzeta.div hden hnu)).circleIntegrable hR
  have hC : CircleIntegrable C c R :=
    (((continuousOn_const.sub continuousOn_id).div hw hw0).mul hchi).circleIntegrable hR
  have hE : CircleIntegrable E c R :=
    (((continuousOn_id.sub continuousOn_const).mul (hzeta.sub hchi)).div hw hw0).circleIntegrable hR
  have hQ : CircleIntegrable Q c R :=
    ((((continuousOn_id.sub continuousOn_const).pow 2).mul hzeta).div (hden.mul hw)
      (fun z hz => mul_ne_zero (hnu z hz) (hw0 z hz))).circleIntegrable hR
  have he : (∮ z in C(c,R), (sigma-rho)*N z) =
      ∮ z in C(c,R), ((nu-rho)*P z+E z)+Q z-C z := by
    apply circleIntegral.integral_congr hR
    intro z hz
    dsimp only [N,P,E,Q,C]
    field_simp [hw0 z hz,hnu z hz]
    ring
  have hNP : CircleIntegrable (fun z => (nu-rho)*P z) c R := hP.const_mul _
  have hPE : CircleIntegrable (fun z => (nu-rho)*P z+E z) c R := hNP.add hE
  have hPEQ : CircleIntegrable (fun z => ((nu-rho)*P z+E z)+Q z) c R := hPE.add hQ
  change (∮ z in C(c,R), P z) = 0 at hpsi
  change (∮ z in C(c,R), C z) = 0 at hcritical
  rw [circleIntegral.integral_const_mul,
    circleIntegral.integral_sub hPEQ hC,
    circleIntegral.integral_add hPE hQ,
    circleIntegral.integral_add hNP hE,
    circleIntegral.integral_const_mul,hpsi,hcritical] at he
  simpa only [mul_zero,zero_add,sub_zero,N,E,Q] using he

/-- A quantitative root bound follows once the normalizing period is bounded away from zero. -/
theorem norm_root_difference_le_of_period_identity
    (sigma rho A E Q : ℂ) (kappa e q : ℝ) (hkappa : 0 < kappa)
    (hA : kappa ≤ ‖A‖) (hE : ‖E‖ ≤ e) (hQ : ‖Q‖ ≤ q)
    (hid : (sigma-rho)*A = E+Q) :
    ‖sigma-rho‖ ≤ (e+q)/kappa := by
  apply (le_div_iff₀ hkappa).mpr
  calc
    ‖sigma-rho‖*kappa ≤ ‖sigma-rho‖*‖A‖ := mul_le_mul_of_nonneg_left hA (norm_nonneg _)
    _ = ‖E+Q‖ := by rw [← norm_mul,hid]
    _ ≤ ‖E‖+‖Q‖ := norm_add_le _ _
    _ ≤ e+q := add_le_add hE hQ
end NLS.ComplexAnalysis
