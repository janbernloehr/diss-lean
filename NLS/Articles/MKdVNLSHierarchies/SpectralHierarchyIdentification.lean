import NLS.MKdV.SpectralMiuraHamiltonians
import NLS.Articles.MKdVNLSHierarchies.FiniteGapHamiltonianIdentification

/-! # Theorem 1 for the physical spectral hierarchy on its full domains

The scalar Hamiltonians are uniquely determined by coefficient limits of
the independent physical Hill discriminant on all smooth complex profiles
and continuous extension to H^(m-1). These extensions exist and are entire
analytic. Their actual Frechet gradients and distribution derivatives
give the original full-domain flow comparison, including the L2 endpoint.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat NLS.Fourier
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- No spectral extension is an input hypothesis: its existence,
uniqueness on the full native complex space, and analyticity are proved. -/
theorem spectral_hierarchy_native_identification (s : ℕ) :
    IsMiuraSpectralHamiltonianExtension s (miuraSpectralHillHamiltonian s) ∧
      (∀ u : ScalarSobolev s, AnalyticAt ℂ (miuraSpectralHillHamiltonian s) u) ∧
      ∀ F : ScalarSobolev s → ℂ, IsMiuraSpectralHamiltonianExtension s F →
        F = miuraSpectralHillHamiltonian s := by
  refine ⟨miuraSpectralHillHamiltonian_spec s,analyticAt_miuraSpectralHillHamiltonian s,?_⟩
  intro F hF
  exact (existsUnique_miuraSpectralHamiltonianExtension s).unique hF (miuraSpectralHillHamiltonian_spec s)

/-- Proposition 6 with the physical spectral scalar Hamiltonian on the
complete original complex H^(m-1) domain, and even vanishing on H^m. -/
theorem proposition6 (m : ℕ) (hm : 1 ≤ m) :
    (∀ u : ScalarSobolev (m-1), sharpOddNLSHamiltonian (m-1) (u,u) =
      2*miuraSpectralHillHamiltonian (m-1) u) ∧
    (∀ u : ScalarSobolev m, sobolevEvenHamiltonian m hm (u,u) = 0) := by
  constructor
  · intro u
    rw [miuraSpectralHillHamiltonian_eq_native]
    exact proposition6_native_miura m hm u
  · exact theorem1_even_vanishing_sharp m hm

/-- Theorem 1 on every original complex H^m input. The scalar field is
Gardner's actual distribution derivative of the actual native Frechet
gradient of the uniquely extended physical spectral Hamiltonian. -/
theorem theorem1 (m : ℕ) (hm : 1 ≤ m) (u : ScalarSobolev m) :
    sobolevEvenHamiltonian m hm (u,u) = 0 ∧
      (periodOneSobolevDistribution (-(m : ℝ)) (sobolevEvenHierarchyVectorField m hm (u,u)).1,
        periodOneSobolevDistribution (-(m : ℝ)) (sobolevEvenHierarchyVectorField m hm (u,u)).2) =
        (miuraSpectralHillVectorField (m-1) (hierarchySobolevInclusion m (m-1) (by omega) u),
          miuraSpectralHillVectorField (m-1) (hierarchySobolevInclusion m (m-1) (by omega) u)) := by
  rw [miuraSpectralHillVectorField_eq_native]
  exact theorem1_native_miura_hierarchy m hm u

/-- The source's actual finite-gap Hill primitive uses precisely these
uniquely extended spectral Hamiltonians, with its exact factor two. -/
theorem equation12_spectral_native_laurent (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 < z.re → R < ‖z‖ →
      HasSum (fun k : ℕ => I*(2*miuraSpectralHillHamiltonian k (miuraFiniteGapSobolev a ha hf k)) /
        (2*z)^(2*k+1)) (canonicalMiuraHillPrimitive a (z^2)+I*z) := by
  simp_rw [miuraSpectralHillHamiltonian_eq_native]
  exact equation12_finiteGap_native_laurent a ha hf

end NLS.Articles.MKdVNLSHierarchies
