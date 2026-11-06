import NLS.MKdV.SobolevMiuraPrimitive
import NLS.Articles.MKdVNLSHierarchies.DiscriminantIdentity

/-! # The physical Hill primitive on the original H¹ domain

The root and primitive are independent source-continuation constructions
from the physical quasi-Hill IVP. Lemmas 4 and 5 are proved on the full real
H¹ domain at nonreal frequencies in the right half-plane. Extension to the
entire labeled gap complement is a separate remaining obligation.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

def hillRoot (a : ScalarDomain 2) (μ : ℂ) : ℂ := miuraHillRoot (μ,periodOneMiuraCurve a)
def hillPrimitive (a : ScalarDomain 2) (μ : ℂ) : ℂ := miuraHillPrimitive (μ,periodOneMiuraCurve a)

theorem lemma4_root_real_H1_right_halfPlane (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    hillRoot a (z^2) =
      sourceCanonicalRoot (by simp) (by norm_num) (realDiagonalH1Source a ha).val z :=
  (periodOneMiura_sheets_eq_NLS a ha z hzr hzi).1

theorem lemma5_primitive_real_H1_right_halfPlane (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    hillPrimitive a (z^2) = sourceAbelianPrimitive (by simp) (by norm_num)
      (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property z :=
  (periodOneMiura_sheets_eq_NLS a ha z hzr hzi).2

theorem hillPrimitive_physical_trace (a : ScalarDomain 2) (μ : ℂ)
    (ht : (μ,periodOneMiuraCurve a) ∈ miuraHillContinuationDomain) :
    2*cosh (hillPrimitive a μ) = hillDiscriminant a μ ∧
      2*sinh (hillPrimitive a μ) = hillRoot a μ := by
  rw [hillDiscriminant,physicalMiuraDiscriminant_eq_quasiHill _ (periodOneMiuraCurve_endpoints a)]
  exact miuraHillPrimitive_trace _ ht

theorem hillPrimitive_hasDerivAt (a : ScalarDomain 2) (μ : ℂ)
    (ht : (μ,periodOneMiuraCurve a) ∈ miuraHillContinuationDomain) :
    HasDerivAt (hillPrimitive a) (deriv (hillDiscriminant a) μ / hillRoot a μ) μ := by
  have he : hillDiscriminant a = quasiHillDiscriminant (periodOneMiuraCurve a) := by
    funext z
    exact physicalMiuraDiscriminant_eq_quasiHill _ (periodOneMiuraCurve_endpoints a) z
  rw [he]
  simpa only [hillPrimitive,hillRoot] using!
    (hasDerivAt_miuraHillPrimitive (μ,periodOneMiuraCurve a) ht)

end NLS.Articles.MKdVNLSHierarchies
