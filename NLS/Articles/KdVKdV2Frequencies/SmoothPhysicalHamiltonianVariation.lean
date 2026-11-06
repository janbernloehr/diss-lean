import NLS.Articles.KdVKdV2Frequencies.SmoothKdVIdentities
import NLS.KdV.NativeHamiltonianPhysicalIntegrals
import NLS.DifferentialPolynomial.SmoothVariation
import NLS.DifferentialPolynomial.EulerFiniteSum

/-! # Actual complex first variations of the printed physical KdV Hamiltonians

The existing formal Euler identities are connected to the independent
physical integrals, with their exact one-half factors. Differentiation is
justified in the continuous-function Banach algebra, before integration by parts.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory MvPolynomial NLS.KdV NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies

theorem twiceKdVDensity_vars_subset : twiceKdVDensity.vars ⊆ {(false,0),(false,1)} := by
  classical
  let S : Finset Jet := {(false,0),(false,1)}
  have h0 : (scalarJet 0).vars ⊆ S := by simp [S,scalarJet]
  have h1 : (scalarJet 1).vars ⊆ S := by simp [S,scalarJet]
  have hc : (2 : Polynomial).vars ⊆ S := by
    change (C (2 : ℂ)).vars ⊆ S
    simp
  apply (vars_add_subset _ _).trans
  apply Finset.union_subset
  · exact (vars_pow _ _).trans h1
  · exact (vars_mul _ _).trans (Finset.union_subset hc ((vars_pow _ _).trans h0))

theorem twiceKdV2Density_vars_subset : twiceKdV2Density.vars ⊆ {(false,0),(false,1),(false,2)} := by
  classical
  let S : Finset Jet := {(false,0),(false,1),(false,2)}
  have h0 : (scalarJet 0).vars ⊆ S := by simp [S,scalarJet]
  have h1 : (scalarJet 1).vars ⊆ S := by simp [S,scalarJet]
  have h2 : (scalarJet 2).vars ⊆ S := by simp [S,scalarJet]
  have hc10 : (10 : Polynomial).vars ⊆ S := by
    change (C (10 : ℂ)).vars ⊆ S
    simp
  have hc5 : (5 : Polynomial).vars ⊆ S := by
    change (C (5 : ℂ)).vars ⊆ S
    simp
  have h10 : (10*scalarJet 0).vars ⊆ S := (vars_mul _ _).trans (Finset.union_subset hc10 h0)
  apply (vars_add_subset _ _).trans
  apply Finset.union_subset
  · apply (vars_add_subset _ _).trans
    exact Finset.union_subset ((vars_pow _ _).trans h2)
      ((vars_mul _ _).trans (Finset.union_subset h10 ((vars_pow _ _).trans h1)))
  · exact (vars_mul _ _).trans (Finset.union_subset hc5 ((vars_pow _ _).trans h0))

/-- The generic Euler operator gives the already calibrated first physical gradient. -/
theorem eulerDerivative_twiceKdVDensity : eulerDerivative false twiceKdVDensity = 2*kdvGradient := by
  classical
  calc
    _ = pderiv (false,0) twiceKdVDensity-spatialDerivative (pderiv (false,1) twiceKdVDensity) := by
      rw [eulerDerivative_eq_sum_of_vars_subset false twiceKdVDensity _ twiceKdVDensity_vars_subset]
      simp [sub_eq_add_neg]
    _ = _ := euler_twiceKdVDensity

/-- The actual generic Euler operator has the exact printed second physical gradient. -/
theorem eulerDerivative_twiceKdV2Density : eulerDerivative false twiceKdV2Density = 2*kdv2Gradient := by
  classical
  calc
    _ = pderiv (false,0) twiceKdV2Density-spatialDerivative (pderiv (false,1) twiceKdV2Density)+
        spatialDerivative (spatialDerivative (pderiv (false,2) twiceKdV2Density)) := by
      rw [eulerDerivative_eq_sum_of_vars_subset false twiceKdV2Density _ twiceKdV2Density_vars_subset]
      simp [sub_eq_add_neg,Function.iterate_succ_apply']
      ring
    _ = _ := euler_twiceKdV2Density

/-- The independent printed H1 is half the physical period integral of the density. -/
theorem classicalHamiltonian_eq_half_integral_twiceDensity (f : ℝ → ℂ) :
    classicalHamiltonian f = (1/2 : ℂ)*∫ x in (0 : ℝ)..1, evaluate f 0 twiceKdVDensity x := by
  rw [classicalHamiltonian,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  simp [evaluate,twiceKdVDensity,iteratedDeriv_one]
  ring

/-- The independent printed H2 retains its exact one-half normalization. -/
theorem classicalKdV2Hamiltonian_eq_half_integral_twiceDensity (f : ℝ → ℂ) :
    classicalKdV2Hamiltonian f = (1/2 : ℂ)*∫ x in (0 : ℝ)..1, evaluate f 0 twiceKdV2Density x := by
  rw [classicalKdV2Hamiltonian,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  simp [evaluate,twiceKdV2Density,iteratedDeriv_succ]
  ring

/-- The actual complex first variation of printed H1 is its physical Euler gradient. -/
theorem hasDerivAt_classicalHamiltonian_variation (f h : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (hpf : Function.Periodic f 1) (hph : Function.Periodic h 1) :
    HasDerivAt (fun c : ℂ => classicalHamiltonian (fun x => f x+c*h x))
      (∫ x in (0 : ℝ)..1, h x*evaluate f 0 kdvGradient x) 0 := by
  have hd := (hasDerivAt_integral_evaluate_euler f 0 h 0 hf contDiff_const hh contDiff_const
    hpf (fun _ => rfl) hph (fun _ => rfl) twiceKdVDensity).const_mul (1/2 : ℂ)
  have he : (fun c : ℂ => (1/2 : ℂ)*∫ x in (0 : ℝ)..1,
      evaluate (fun t => f t+c*h t) (fun t => (0 : ℂ)+c*0) twiceKdVDensity x) =
      fun c : ℂ => classicalHamiltonian (fun t => f t+c*h t) := by
    funext c
    simp only [mul_zero,add_zero]
    exact (classicalHamiltonian_eq_half_integral_twiceDensity _).symm
  have hv : (1/2 : ℂ)*(∫ x in (0 : ℝ)..1,
      h x*evaluate f 0 (eulerDerivative false twiceKdVDensity) x+
        (0 : ℂ)*evaluate f 0 (eulerDerivative true twiceKdVDensity) x) =
      ∫ x in (0 : ℝ)..1, h x*evaluate f 0 kdvGradient x := by
    rw [eulerDerivative_twiceKdVDensity,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    simp [evaluate]
    ring
  simpa only [Pi.zero_apply,he,hv] using! hd

/-- The actual complex first variation of printed H2 has all original coefficients. -/
theorem hasDerivAt_classicalKdV2Hamiltonian_variation (f h : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (hpf : Function.Periodic f 1) (hph : Function.Periodic h 1) :
    HasDerivAt (fun c : ℂ => classicalKdV2Hamiltonian (fun x => f x+c*h x))
      (∫ x in (0 : ℝ)..1, h x*evaluate f 0 kdv2Gradient x) 0 := by
  have hd := (hasDerivAt_integral_evaluate_euler f 0 h 0 hf contDiff_const hh contDiff_const
    hpf (fun _ => rfl) hph (fun _ => rfl) twiceKdV2Density).const_mul (1/2 : ℂ)
  have he : (fun c : ℂ => (1/2 : ℂ)*∫ x in (0 : ℝ)..1,
      evaluate (fun t => f t+c*h t) (fun t => (0 : ℂ)+c*0) twiceKdV2Density x) =
      fun c : ℂ => classicalKdV2Hamiltonian (fun t => f t+c*h t) := by
    funext c
    simp only [mul_zero,add_zero]
    exact (classicalKdV2Hamiltonian_eq_half_integral_twiceDensity _).symm
  have hv : (1/2 : ℂ)*(∫ x in (0 : ℝ)..1,
      h x*evaluate f 0 (eulerDerivative false twiceKdV2Density) x+
        (0 : ℂ)*evaluate f 0 (eulerDerivative true twiceKdV2Density) x) =
      ∫ x in (0 : ℝ)..1, h x*evaluate f 0 kdv2Gradient x := by
    rw [eulerDerivative_twiceKdV2Density,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    simp [evaluate]
    ring
  simpa only [Pi.zero_apply,he,hv] using! hd

end NLS.Articles.KdVKdV2Frequencies
