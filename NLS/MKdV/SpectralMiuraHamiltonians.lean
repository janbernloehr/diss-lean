import NLS.MKdV.NativeMiuraHillGradient
import NLS.MKdV.MiuraHillHamiltonianTrace
import NLS.ZakharovShabat.NLSHamiltonianSpectralCoefficients

/-! # The uniquely extended physical spectral mKdV hierarchy

On smooth complex profiles, the Hamiltonians are extracted recursively
from the independent physical Hill monodromy trace. Their unique
continuous extensions to the complete native complex H^s spaces exist
and are entire analytic. The independent scalar Riccati construction
realizes these extensions; it is not an assumed spectral identification.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff SchwartzMap
namespace NLS.MKdV

/-- The source K_(s+1) normalization of the actual odd trace coefficient.
Only physical Hill IVP data, fixed lattice samples, a small inverse sinh,
and recursive limits enter this definition. -/
def smoothMiuraSpectralHamiltonian (f : ℝ → ℂ) (hf : Continuous f) (s : ℕ) : ℂ :=
  (-I/2)*sampledPhaseCoefficient
    (fun r => physicalMiuraDiscriminant (miuraProfileCurve f hf) ((r : ℂ)^2)) (2*s)

theorem smoothMiuraSpectralHamiltonian_eq_classical (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (s : ℕ) :
    smoothMiuraSpectralHamiltonian f hf.continuous s = classicalMiuraHillHamiltonian f (s+1) := by
  have ht : (fun r : ℝ => physicalMiuraDiscriminant (miuraProfileCurve f hf.continuous) ((r : ℂ)^2)) =
      (fun r : ℝ => classicalDiscriminant (classicalPotentialOfFunctions f f hf.continuous hf.continuous) r) :=
    funext (fun r => physicalMiuraDiscriminant_profile_eq_ZS f hf.continuous hp r)
  rw [smoothMiuraSpectralHamiltonian,ht,
    sampledPhaseCoefficient_classicalDiscriminant f f hf hf hp hp,
    classicalNLSHamiltonian_odd_diagonal_eq_miuraHill f hf hp s]
  calc
    (-I/2)*(I*(2*classicalMiuraHillHamiltonian f (s+1))) =
        -(I^2)*classicalMiuraHillHamiltonian f (s+1) := by ring
    _ = classicalMiuraHillHamiltonian f (s+1) := by rw [I_sq]; ring

/-- Agreement with actual physical spectral coefficient limits on all
smooth complex profiles, together with continuity on the native space. -/
def IsMiuraSpectralHamiltonianExtension (s : ℕ) (F : ScalarSobolev s → ℂ) : Prop :=
  Continuous F ∧ ∀ (u : ScalarSobolev s) (f : ℝ → ℂ),
    ∀ hf : ContDiff ℝ ∞ f, Function.Periodic f 1 →
      (∀ j, u.val j = periodOneCoefficient f j) → F u = smoothMiuraSpectralHamiltonian f hf.continuous s

theorem nativeMiuraHillHamiltonian_spectral_extension (s : ℕ) :
    IsMiuraSpectralHamiltonianExtension s (nativeMiuraHillHamiltonian s) := by
  refine ⟨continuous_iff_continuousAt.mpr (fun u =>
    (analyticAt_nativeMiuraHillHamiltonian s u).continuousAt),?_⟩
  intro u f hf hp hc
  exact (nativeMiuraHillHamiltonian_eq_classical s u f hf hp hc).trans
    (smoothMiuraSpectralHamiltonian_eq_classical f hf hp s).symm

/-- Existence and uniqueness on the full complex H^s native domain,
including s=0. Smooth density suffices; no diagonal finite-gap density
or unproved continuity of a spectral extension is assumed. -/
theorem existsUnique_miuraSpectralHamiltonianExtension (s : ℕ) :
    ∃! F : ScalarSobolev s → ℂ, IsMiuraSpectralHamiltonianExtension s F := by
  refine ⟨nativeMiuraHillHamiltonian s,nativeMiuraHillHamiltonian_spectral_extension s,?_⟩
  intro F hF
  apply nativeMiuraHillHamiltonian_unique_continuous s F hF.1
  intro u f hf hp hc
  exact (hF.2 u f hf hp hc).trans (smoothMiuraSpectralHamiltonian_eq_classical f hf hp s)

/-- The native spectral Hamiltonian is selected by the spectral extension
property, independently of any NLS restriction identity. -/
def miuraSpectralHillHamiltonian (s : ℕ) : ScalarSobolev s → ℂ :=
  Classical.choose (existsUnique_miuraSpectralHamiltonianExtension s).exists

theorem miuraSpectralHillHamiltonian_spec (s : ℕ) :
    IsMiuraSpectralHamiltonianExtension s (miuraSpectralHillHamiltonian s) :=
  Classical.choose_spec (existsUnique_miuraSpectralHamiltonianExtension s).exists

theorem miuraSpectralHillHamiltonian_eq_native (s : ℕ) :
    miuraSpectralHillHamiltonian s = nativeMiuraHillHamiltonian s :=
  (existsUnique_miuraSpectralHamiltonianExtension s).unique
    (miuraSpectralHillHamiltonian_spec s) (nativeMiuraHillHamiltonian_spectral_extension s)

theorem analyticAt_miuraSpectralHillHamiltonian (s : ℕ) (u : ScalarSobolev s) :
    AnalyticAt ℂ (miuraSpectralHillHamiltonian s) u := by
  rw [miuraSpectralHillHamiltonian_eq_native]
  exact analyticAt_nativeMiuraHillHamiltonian s u

def miuraSpectralHillGradient (s : ℕ) (u : ScalarSobolev s) : NegativeScalarSobolev s :=
  WeightedCoeff.sobolevCotangentCLM (p := 2) (q := 2) (s : ℝ) (by norm_num)
    (fderiv ℂ (miuraSpectralHillHamiltonian s) u)

theorem miuraSpectralHillGradient_represents (s : ℕ) (u h : ScalarSobolev s) :
    WeightedCoeff.sobolevBilinearPairing (s : ℝ) h (miuraSpectralHillGradient s u) =
      fderiv ℂ (miuraSpectralHillHamiltonian s) u h := by
  rw [miuraSpectralHillGradient,WeightedCoeff.sobolevCotangentCLM_apply,
    WeightedCoeff.sobolevBilinearPairing_sobolevCotangent]

theorem miuraSpectralHillGradient_eq_native (s : ℕ) :
    miuraSpectralHillGradient s = nativeMiuraHillGradient s := by
  unfold miuraSpectralHillGradient nativeMiuraHillGradient
  rw [miuraSpectralHillHamiltonian_eq_native]

def miuraSpectralHillVectorField (s : ℕ) (u : ScalarSobolev s) : 𝓢'(ℝ,ℂ) :=
  TemperedDistribution.derivCLM ℂ (periodOneSobolevDistribution (-(s : ℝ)) (miuraSpectralHillGradient s u))

theorem miuraSpectralHillVectorField_eq_native (s : ℕ) :
    miuraSpectralHillVectorField s = nativeMiuraHillVectorField s := by
  unfold miuraSpectralHillVectorField nativeMiuraHillVectorField
  rw [miuraSpectralHillGradient_eq_native]

end NLS.MKdV
