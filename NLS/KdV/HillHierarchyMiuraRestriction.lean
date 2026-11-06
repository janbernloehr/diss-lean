import NLS.DifferentialPolynomial.FieldJetSubstitution
import NLS.KdV.NativeHillHierarchyHamiltonian
import NLS.KdV.NativeMiuraPhysicalHamiltonians

/-! # All-order physical Miura restriction of the original KdV hierarchy

Complete jet substitution identifies the independently seeded scalar
recurrences. The equality extends to the full original complex H^(m+1)
factor domain by verified native smooth density and continuity.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.ZakharovShabat NLS.MKdV NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.KdV

/-- Substituting the actual Miura potential intertwines the two independent
scalar Riccati recurrences at every coefficient. -/
theorem hillRiccatiPolynomial_miura_substitution (n : ℕ) :
    fieldJetSubstitution (fun _ => miuraHillPotentialPolynomial) (hillRiccatiPolynomial n) =
      miuraHillRiccatiPolynomial n :=
  fieldJetSubstitution_scalarRiccati _ n

/-- Physical evaluation uses every actual derivative of u_x+u^2. -/
theorem evaluate_hillRiccatiPolynomial_miura (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    evaluate u u (miuraHillRiccatiPolynomial n) =
      evaluate (fun x => deriv u x+(u x)^2) (fun x => deriv u x+(u x)^2) (hillRiccatiPolynomial n) := by
  have he := evaluate_fieldJetSubstitution u u hu hu (fun _ => miuraHillPotentialPolynomial)
    (hillRiccatiPolynomial n)
  simpa only [hillRiccatiPolynomial_miura_substitution,evaluate_miuraHillPotentialPolynomial] using he

/-- The independently defined scalar Miura member K_(m+2) is exactly the
original physical KdV member H_m at the actual Miura potential. -/
theorem classicalMiuraHillHamiltonian_eq_hillHierarchy (m : ℕ) (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) :
    classicalMiuraHillHamiltonian u (m+2) =
      classicalHillHierarchyHamiltonian (fun x => deriv u x+(u x)^2) m := by
  change ((-1 : ℂ)^(m+2)/2)*
    (∫ x in (0 : ℝ)..1, evaluate u u (miuraHillRiccatiPolynomial (2*(m+1))) x) = _
  rw [show 2*(m+1)=2*m+2 by omega,evaluate_hillRiccatiPolynomial_miura u hu]
  rfl

/-- All-order Miura restriction on EVERY original complex H^(m+1) factor.
No smoothness, reality or zero-mean hypothesis remains. -/
theorem nativeHillHierarchyHamiltonian_miura (m : ℕ) (u : ScalarSobolev (m+1)) :
    nativeHillHierarchyHamiltonian m (nativeMiuraPotential m u) =
      nativeMiuraHillHamiltonian (m+1) u := by
  have he := eq_of_continuous_of_smooth_scalarSobolev (m+1)
    (fun v => nativeHillHierarchyHamiltonian m (nativeMiuraPotential m v)) (nativeMiuraHillHamiltonian (m+1))
    ((continuous_iff_continuousAt.mpr fun q => (analyticAt_nativeHillHierarchyHamiltonian m q).continuousAt).comp
      (continuous_iff_continuousAt.mpr fun v => (analyticAt_nativeMiuraPotential m v).continuousAt))
    (continuous_iff_continuousAt.mpr fun v => (analyticAt_nativeMiuraHillHamiltonian (m+1) v).continuousAt) (by
      intro v f hf hp hc
      have hd := (contDiff_infty_iff_deriv.mp hf).2
      have hper : Function.Periodic (fun x => deriv f x+(f x)^2) 1 := by
        intro x
        change deriv f (x+1)+(f (x+1))^2 = deriv f x+(f x)^2
        rw [NLS.ZakharovShabat.periodic_deriv_of_periodic f 1 hp x,hp x]
      rw [nativeHillHierarchyHamiltonian_eq_classical m _ _ (hd.add (hf.pow 2)) hper
        (nativeMiuraPotential_classical_coefficients m v f hf hp hc),
        nativeMiuraHillHamiltonian_eq_classical (m+1) v f hf hp hc]
      exact (classicalMiuraHillHamiltonian_eq_hillHierarchy m f hf).symm)
  exact congrFun he u

end NLS.KdV
