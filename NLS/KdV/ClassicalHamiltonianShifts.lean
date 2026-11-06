import NLS.KdV.NativeHamiltonianPhysicalIntegrals
import NLS.MKdV.HierarchyRestriction

/-! # Exact constant-shift identities of the printed physical Hamiltonians -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.MKdV
open scoped ContDiff
namespace NLS.KdV

/-- The physical quadratic mass retains its mean term under a constant shift. -/
theorem classicalMKdVMass_add_const (q : ℝ → ℂ) (hq : Continuous q) (c : ℂ) :
    classicalMKdVMass (fun x => q x+c) = classicalMKdVMass q+
      c*(∫ x in (0 : ℝ)..1, q x)+c^2/2 := by
  unfold classicalMKdVMass
  have he : (fun x => (q x+c)^2) = fun x => (q x)^2+2*c*q x+c^2 := by
    funext x
    ring
  rw [he]
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
  norm_num
  ring

/-- H1 has the exact coefficients 6, 3 and 1 in its constant-shift formula. -/
theorem classicalHamiltonian_add_const (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (c : ℂ) :
    classicalHamiltonian (fun x => q x+c) = classicalHamiltonian q+
      6*c*classicalMKdVMass q+3*c^2*(∫ x in (0 : ℝ)..1, q x)+c^3 := by
  have hd : deriv (fun x => q x+c) = deriv q := by
    funext x
    exact ((hq.differentiable (by simp) x).hasDerivAt.add_const c).deriv
  have hdc := (contDiff_infty_iff_deriv.mp hq).2.continuous
  unfold classicalHamiltonian classicalMKdVMass
  rw [hd]
  have he : (fun x => (deriv q x)^2/2+(q x+c)^3) =
      fun x => ((deriv q x)^2/2+(q x)^3)+3*c*(q x)^2+3*c^2*q x+c^3 := by
    funext x
    ring
  rw [he]
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
  norm_num
  ring

/-- H2 has the exact coefficients 10, 30, 10 and 5/2, retaining the mean. -/
theorem classicalKdV2Hamiltonian_add_const (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (c : ℂ) :
    classicalKdV2Hamiltonian (fun x => q x+c) = classicalKdV2Hamiltonian q+
      10*c*classicalHamiltonian q+30*c^2*classicalMKdVMass q+
        10*c^3*(∫ x in (0 : ℝ)..1, q x)+(5/2 : ℂ)*c^4 := by
  have hd : deriv (fun x => q x+c) = deriv q := by
    funext x
    exact ((hq.differentiable (by simp) x).hasDerivAt.add_const c).deriv
  have hdc := (contDiff_infty_iff_deriv.mp hq).2.continuous
  have hddc := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hq).2).2.continuous
  unfold classicalKdV2Hamiltonian classicalHamiltonian classicalMKdVMass
  rw [hd]
  have he : (fun x => (deriv (deriv q) x)^2/2+5*(q x+c)*(deriv q x)^2+(5/2 : ℂ)*(q x+c)^4) =
      fun x => ((deriv (deriv q) x)^2/2+5*q x*(deriv q x)^2+(5/2 : ℂ)*(q x)^4)+
        10*c*((deriv q x)^2/2+(q x)^3)+15*c^2*(q x)^2+10*c^3*q x+(5/2 : ℂ)*c^4 := by
    funext x
    ring
  rw [he]
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
  norm_num
  ring

end NLS.KdV
