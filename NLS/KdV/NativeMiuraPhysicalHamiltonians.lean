import NLS.KdV.MiuraPhysicalHamiltonians
import NLS.MKdV.NativeMiuraHillHamiltonian
import NLS.SequenceSpaces.PeriodOneMiuraInverseCompact
import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra

/-! # Physical Miura restriction on the full native KdV domains

The actual coefficient Miura map H^(s+1) -> H^s is complex analytic.
Smooth physical identities extend by continuity and the verified native
smooth density, with no smoothness assumption on the resulting identities.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.ZakharovShabat NLS.MKdV
open scoped ContDiff
namespace NLS.KdV

/-- The literal unshifted Miura potential in the original integer native spaces. -/
def nativeMiuraPotential (s : ℕ) (u : ScalarSobolev (s+1)) : ScalarSobolev s :=
  WeightedCoeff.sobolevInclusion (by push_cast; linarith : (s : ℝ) ≤ ((s+1 : ℕ) : ℝ)-1)
    (periodOneSobolevMiura ((s+1 : ℕ) : ℝ) (by positivity) u)

theorem analyticAt_nativeMiuraPotential (s : ℕ) (u : ScalarSobolev (s+1)) :
    AnalyticAt ℂ (nativeMiuraPotential s) u := by
  let t : ℝ := ((s+1 : ℕ) : ℝ)
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hM : AnalyticAt ℂ (periodOneSobolevMiura t ht) u :=
    (analyticAt_periodOneSobolevShiftedMiura 0 t ht u).sub
      ((WeightedCoeff.sobolevInclusion (by dsimp [t]; push_cast; linarith : t-1 ≤ t)).analyticAt u)
  exact (WeightedCoeff.sobolevInclusion
    (by dsimp [t]; push_cast; linarith : (s : ℝ) ≤ t-1)).analyticAt _ |>.comp hM

/-- Every signed coefficient has the exact unit-period derivative and convolution. -/
theorem nativeMiuraPotential_apply (s : ℕ) (u : ScalarSobolev (s+1)) (n : ℤ) :
    (nativeMiuraPotential s u).val n = 2*I*(Real.pi : ℂ)*n*u.val n+
      ∑' j : ℤ, u.val (n-j)*u.val j := by
  simp only [nativeMiuraPotential,WeightedCoeff.sobolevInclusion_apply,
    periodOneSobolevMiura_apply_toL2,periodOneMiura_apply,WeightedCoeff.sobolevToL2_apply]

/-- Smooth comparison uses the original physical Fourier integrals. -/
theorem nativeMiuraPotential_classical_coefficients (s : ℕ) (u : ScalarSobolev (s+1))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ n, u.val n = periodOneCoefficient f n) (n : ℤ) :
    (nativeMiuraPotential s u).val n =
      periodOneCoefficient (fun x => deriv f x+(f x)^2) n := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have he : (fun x => deriv f x+(f x)^2) = deriv f+f*f := by
    funext x
    simp only [Pi.add_apply,Pi.mul_apply,pow_two]
  rw [nativeMiuraPotential_apply,he,periodOneCoefficient_add _ _ hd.continuous
    (hf.continuous.mul hf.continuous),periodOneCoefficient_deriv_of_smooth_periodic f hf hp,
    periodOneCoefficient_mul_of_smooth_periodic f f hf hf hp hp]
  simp only [hc]

/-- The original quadratic mass of the actual Miura potential equals K2
on the FULL complex H1 factor domain. -/
theorem nativeMiuraMass_miura (u : ScalarSobolev 1) :
    nativeMiuraMass 0 (nativeMiuraPotential 0 u) = nativeMiuraHillHamiltonian 1 u := by
  have he := eq_of_continuous_of_smooth_scalarSobolev 1
    (fun v => nativeMiuraMass 0 (nativeMiuraPotential 0 v)) (nativeMiuraHillHamiltonian 1)
    ((continuous_iff_continuousAt.mpr fun q => (analyticAt_nativeMiuraMass 0 q).continuousAt).comp
      (continuous_iff_continuousAt.mpr fun v => (analyticAt_nativeMiuraPotential 0 v).continuousAt))
    (continuous_iff_continuousAt.mpr fun v => (analyticAt_nativeMiuraHillHamiltonian 1 v).continuousAt) (by
      intro v f hf hp hc
      have hd := (contDiff_infty_iff_deriv.mp hf).2
      have hper : Function.Periodic (fun x => deriv f x+(f x)^2) 1 := by
        intro x
        change deriv f (x+1)+(f (x+1))^2 = deriv f x+(f x)^2
        rw [NLS.ZakharovShabat.periodic_deriv_of_periodic f 1 hp x,hp x]
      rw [nativeMiuraMass_eq_classical 0 _ _ (hd.add (hf.pow 2))
        hper (nativeMiuraPotential_classical_coefficients 0 v f hf hp hc),
        nativeMiuraHillHamiltonian_eq_classical 1 v f hf hp hc,
        classicalMiuraHillHamiltonian_one _ (hd.add (hf.pow 2)) hper]
      exact (classicalMiuraHillHamiltonian_two_eq_miura_mass f hf hp).symm)
  exact congrFun he u

/-- Printed H1 at the actual Miura potential equals the independently defined
K3 at EVERY complex H2 factor, including arbitrary nonsmooth factors. -/
theorem nativeKdVHamiltonian_miura (u : ScalarSobolev 2) :
    nativeKdVHamiltonian (nativeMiuraPotential 1 u) = nativeMiuraHillHamiltonian 2 u := by
  have he := eq_of_continuous_of_smooth_scalarSobolev 2
    (fun v => nativeKdVHamiltonian (nativeMiuraPotential 1 v)) (nativeMiuraHillHamiltonian 2)
    ((continuous_iff_continuousAt.mpr fun q => (analyticAt_nativeKdVHamiltonian q).continuousAt).comp
      (continuous_iff_continuousAt.mpr fun v => (analyticAt_nativeMiuraPotential 1 v).continuousAt))
    (continuous_iff_continuousAt.mpr fun v => (analyticAt_nativeMiuraHillHamiltonian 2 v).continuousAt) (by
      intro v f hf hp hc
      have hd := (contDiff_infty_iff_deriv.mp hf).2
      have hper : Function.Periodic (fun x => deriv f x+(f x)^2) 1 := by
        intro x
        change deriv f (x+1)+(f (x+1))^2 = deriv f x+(f x)^2
        rw [NLS.ZakharovShabat.periodic_deriv_of_periodic f 1 hp x,hp x]
      rw [nativeKdVHamiltonian_eq_of_coefficients _ _ (hd.continuous.add (hf.continuous.pow 2))
        hper (nativeMiuraPotential_classical_coefficients 1 v f hf hp hc),
        nativeMiuraHillHamiltonian_eq_classical 2 v f hf hp hc]
      exact (classicalMiuraHillHamiltonian_three f hf hp).symm)
  exact congrFun he u

/-- Printed H2 at the actual Miura potential equals independently defined K4
at EVERY complex H3 factor, with all original coefficients retained. -/
theorem nativeKdV2Hamiltonian_miura (u : ScalarSobolev 3) :
    nativeKdV2Hamiltonian (nativeMiuraPotential 2 u) = nativeMiuraHillHamiltonian 3 u := by
  have he := eq_of_continuous_of_smooth_scalarSobolev 3
    (fun v => nativeKdV2Hamiltonian (nativeMiuraPotential 2 v)) (nativeMiuraHillHamiltonian 3)
    ((continuous_iff_continuousAt.mpr fun q => (analyticAt_nativeKdV2Hamiltonian q).continuousAt).comp
      (continuous_iff_continuousAt.mpr fun v => (analyticAt_nativeMiuraPotential 2 v).continuousAt))
    (continuous_iff_continuousAt.mpr fun v => (analyticAt_nativeMiuraHillHamiltonian 3 v).continuousAt) (by
      intro v f hf hp hc
      have hd := (contDiff_infty_iff_deriv.mp hf).2
      have hper : Function.Periodic (fun x => deriv f x+(f x)^2) 1 := by
        intro x
        change deriv f (x+1)+(f (x+1))^2 = deriv f x+(f x)^2
        rw [NLS.ZakharovShabat.periodic_deriv_of_periodic f 1 hp x,hp x]
      rw [nativeKdV2Hamiltonian_eq_of_coefficients _ _ (hd.continuous.add (hf.continuous.pow 2))
        hper (nativeMiuraPotential_classical_coefficients 2 v f hf hp hc),
        nativeMiuraHillHamiltonian_eq_classical 3 v f hf hp hc]
      exact (classicalMiuraHillHamiltonian_four f hf hp).symm)
  exact congrFun he u

end NLS.KdV
