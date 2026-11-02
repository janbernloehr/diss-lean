import NLS.MKdV.MiuraHillRiccatiRemainder
import NLS.ZakharovShabat.SobolevPolynomialEndpointMean
import NLS.ZakharovShabat.SobolevScalarSmoothDensity
import NLS.ZakharovShabat.SobolevOddHamiltonian

/-! # The independent Hill/Miura Hamiltonians on their native domains

K_(s+1) is constructed on complex H^s by the actual endpoint mean of a
reduced scalar Hill density. The s=0 member is the physical bilinear L²
mass. No member is defined by half a restricted NLS Hamiltonian.
-/
noncomputable section
open MvPolynomial Complex NLS.Fourier NLS.DifferentialPolynomial NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.MKdV

def miuraHillNativePolynomial (s : ℕ) : DifferentialPolynomial.Polynomial :=
  Classical.choose (exists_miuraHillNativePolynomial s)

theorem miuraHillNativePolynomial_order (s : ℕ) : JetOrderLE (miuraHillNativePolynomial s) s :=
  (Classical.choose_spec (exists_miuraHillNativePolynomial s)).1

theorem miuraHillNativePolynomial_derivativeOrder (s : ℕ) :
    DerivativeOrderLE (miuraHillNativePolynomial s) (2*(s : ℤ)) :=
  (Classical.choose_spec (exists_miuraHillNativePolynomial s)).2.1

theorem miuraHillNativePolynomial_classical (s : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    classicalMiuraHillHamiltonian f (s+1) =
      ∫ x in (0 : ℝ)..1, evaluate f f (miuraHillNativePolynomial s) x :=
  (Classical.choose_spec (exists_miuraHillNativePolynomial s)).2.2 f hf hp

def nativeMiuraMass (s : ℕ) (u : ScalarSobolev s) : ℂ :=
  (1/2 : ℂ)*sobolevOddKinetic 0
    (hierarchySobolevInclusion s 0 (by omega) u, hierarchySobolevInclusion s 0 (by omega) u)

theorem analyticAt_nativeMiuraMass (s : ℕ) (u : ScalarSobolev s) :
    AnalyticAt ℂ (nativeMiuraMass s) u := by
  let J : ScalarSobolev s →L[ℂ] SobolevSource 0 :=
    (hierarchySobolevInclusion s 0 (by omega)).prod (hierarchySobolevInclusion s 0 (by omega))
  change AnalyticAt ℂ (fun v => (1/2 : ℂ)*sobolevOddKinetic 0 (J v)) u
  exact analyticAt_const.mul ((analyticAt_sobolevOddKinetic 0 (J u)).comp (f := J) (J.analyticAt u))

theorem nativeMiuraMass_eq_classical (s : ℕ) (u : ScalarSobolev s) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ j, u.val j = periodOneCoefficient f j) :
    nativeMiuraMass s u = classicalMiuraHillHamiltonian f 1 := by
  rw [nativeMiuraMass,sobolevOddKinetic_eq_integral 0 _ f f hf hf hp hp
    (fun j => by simpa only [hierarchySobolevInclusion_apply] using hc j)
    (fun j => by simpa only [hierarchySobolevInclusion_apply] using hc j),
    classicalMiuraHillHamiltonian_one f hf hp]
  simp only [iteratedDeriv_zero,classicalMKdVMass,pow_two]

/-- Native index s means K_(s+1), on the complete original complex H^s space. -/
def nativeMiuraHillHamiltonian (s : ℕ) (u : ScalarSobolev s) : ℂ :=
  if 1 ≤ s then sobolevPolynomialEndpointMean s (miuraHillNativePolynomial s) (u,u)
  else nativeMiuraMass s u

theorem analyticAt_nativeMiuraHillHamiltonian (s : ℕ) (u : ScalarSobolev s) :
    AnalyticAt ℂ (nativeMiuraHillHamiltonian s) u := by
  unfold nativeMiuraHillHamiltonian
  split_ifs
  · exact (analyticAt_sobolevPolynomialEndpointMean s (miuraHillNativePolynomial s) (u,u)).comp
      (f := hierarchyDiagonal s) ((hierarchyDiagonal s).analyticAt u)
  · exact analyticAt_nativeMiuraMass s u

theorem nativeMiuraHillHamiltonian_eq_classical (s : ℕ) (u : ScalarSobolev s) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ j, u.val j = periodOneCoefficient f j) :
    nativeMiuraHillHamiltonian s u = classicalMiuraHillHamiltonian f (s+1) := by
  unfold nativeMiuraHillHamiltonian
  split_ifs with hs
  · rw [miuraHillNativePolynomial_classical s f hf hp]
    exact sobolevPolynomialEndpointMean_eq_classical s hs _
      (miuraHillNativePolynomial_derivativeOrder s) (miuraHillNativePolynomial_order s)
      (u,u) f f hf hf hp hp hc hc
  · rw [show s+1 = 1 by omega]
    exact nativeMiuraMass_eq_classical s u f hf hp hc

/-- The native extension is uniquely determined by the independent physical
scalar hierarchy on smooth inputs, assuming only continuity of a competitor. -/
theorem nativeMiuraHillHamiltonian_unique_continuous (s : ℕ) (F : ScalarSobolev s → ℂ)
    (hF : Continuous F)
    (hclassical : ∀ (u : ScalarSobolev s) (f : ℝ → ℂ), ContDiff ℝ ∞ f → Function.Periodic f 1 →
      (∀ j, u.val j = periodOneCoefficient f j) → F u = classicalMiuraHillHamiltonian f (s+1)) :
    F = nativeMiuraHillHamiltonian s := by
  apply eq_of_continuous_of_smooth_scalarSobolev s F _ hF
    (continuous_iff_continuousAt.mpr fun u => (analyticAt_nativeMiuraHillHamiltonian s u).continuousAt)
  intro u f hf hp hc
  exact (hclassical u f hf hp hc).trans (nativeMiuraHillHamiltonian_eq_classical s u f hf hp hc).symm

theorem nativeMiuraHillHamiltonian_eq_previous (s : ℕ) (u : ScalarSobolev (s+1)) :
    nativeMiuraHillHamiltonian s (hierarchySobolevInclusion (s+1) s (by omega) u) =
      sobolevMiuraHillHamiltonian (s+1) (by omega) u := by
  have he := eq_of_continuous_of_smooth_scalarSobolev (s+1)
    (fun v => nativeMiuraHillHamiltonian s (hierarchySobolevInclusion (s+1) s (by omega) v))
    (sobolevMiuraHillHamiltonian (s+1) (by omega))
    ((continuous_iff_continuousAt.mpr (fun v => (analyticAt_nativeMiuraHillHamiltonian s v).continuousAt)).comp
      (hierarchySobolevInclusion (s+1) s (by omega)).continuous)
    (continuous_iff_continuousAt.mpr (fun v =>
      (analyticAt_sobolevMiuraHillHamiltonian (s+1) (by omega) v).continuousAt)) (by
        intro v f hf hp hc
        rw [nativeMiuraHillHamiltonian_eq_classical s _ f hf hp
          (fun j => by simpa only [hierarchySobolevInclusion_apply] using hc j),
          sobolevMiuraHillHamiltonian_eq_classical (s+1) (by omega) v f hf hp hc])
  exact congrFun he u

/-- Proposition 6's odd identity on the full native complex H^s domain,
including arbitrary nonsmooth sources (s>=1). The mass endpoint is below. -/
theorem nativeMiuraHillHamiltonian_odd_restriction (s : ℕ) (hs : 1 ≤ s) (u : ScalarSobolev s) :
    sobolevOddHamiltonian s hs (u,u) = 2*nativeMiuraHillHamiltonian s u := by
  have he := eq_of_continuous_of_smooth_scalarSobolev s
    (fun v => sobolevOddHamiltonian s hs (v,v)) (fun v => 2*nativeMiuraHillHamiltonian s v)
    ((continuous_sobolevOddHamiltonian s hs).comp (hierarchyDiagonal s).continuous)
    (continuous_const.mul (continuous_iff_continuousAt.mpr fun v =>
      (analyticAt_nativeMiuraHillHamiltonian s v).continuousAt)) (by
        intro v f hf hp hc
        rw [sobolevOddHamiltonian_eq_classical s hs (v,v) f f hf hf hp hp hc hc,
          nativeMiuraHillHamiltonian_eq_classical s v f hf hp hc]
        exact classicalNLSHamiltonian_odd_diagonal_eq_miuraHill f hf hp s)
  exact congrFun he u

theorem nativeMiuraHillHamiltonian_mass_restriction (u : ScalarSobolev 0) :
    sobolevNLSHamiltonian 0 (u,u) 1 (by omega) = 2*nativeMiuraHillHamiltonian 0 u := by
  rw [sobolevNLSHamiltonian_one]
  simp only [nativeMiuraHillHamiltonian,show ¬1 ≤ (0 : ℕ) by omega,↓reduceIte,nativeMiuraMass,
    sobolevOddKinetic,Coeff.dualPairing_apply,Coeff.reflection_apply,hierarchySobolevJetL2_apply,
    hierarchySobolevInclusion_apply,pow_zero,one_mul]
  ring

end NLS.MKdV
