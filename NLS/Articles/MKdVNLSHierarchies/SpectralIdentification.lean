import NLS.MKdV.MiuraHillRealLabels
import NLS.Articles.MKdVNLSHierarchies.DiscriminantIdentity

/-! # The physical L² Hill operator and the article's Miura spectrum

Theorem 5 now uses the shared physical L² Hill monodromy of the literal
Miura potential. The spectral-set and multiplicity parts of Lemma 3 are
also proved. Matching every fixed Hill gap label with its NLS square
remains separate; no action comparison is asserted here.
-/
noncomputable section
open Complex NLS.MKdV NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem theorem5_operator_discriminant_identity (a : ScalarDomain 2) (μ : ℂ) :
    hillL2Discriminant (sobolevMiuraHillPotential a) μ = hillDiscriminant a μ :=
  (hillL2Discriminant_miura a μ).trans
    (physicalMiuraDiscriminant_eq_quasiHill _ (periodOneMiuraCurve_endpoints a) μ).symm

theorem lemma3_spectral_set (a : ScalarDomain 2) (z : ℂ) :
    (∃ f : HillSobolevDomain, f ≠ 0 ∧
      hillOperator (sobolevMiuraHillPotential a) f = z^2 • hillDomainToL2 f) ↔
      z ∈ periodicSpectrum (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) :=
  miuraHill_eigenvector_iff_ZS a z

theorem lemma3_real_spectrum_nonnegative (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ)
    (hμ : hillL2Radicand (sobolevMiuraHillPotential a) μ = 0) : μ.im = 0 ∧ 0 ≤ μ.re :=
  miuraHillRadicand_root_nonnegative a ha μ hμ

theorem lemma3_multiplicity_nonzero (a : ScalarDomain 2) (z : ℂ) (hz : z ≠ 0) :
    analyticOrderNatAt (hillL2Radicand (sobolevMiuraHillPotential a)) (z^2) =
      periodicAlgebraicMultiplicity (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) z :=
  analyticOrderNatAt_miuraHillRadicand_energy a z hz

theorem lemma3_multiplicity_zero (a : ScalarDomain 2) :
    periodicAlgebraicMultiplicity (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) 0 =
      2*analyticOrderNatAt (hillL2Radicand (sobolevMiuraHillPotential a)) 0 :=
  miuraHillRadicand_zero_multiplicity a

end NLS.Articles.MKdVNLSHierarchies
