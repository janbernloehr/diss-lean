import NLS.MKdV.MiuraFiniteGapLaurent
import NLS.Articles.MKdVNLSHierarchies.NativeHierarchy

/-! # Finite-gap spectral Hamiltonian calibration

The finite-gap condition uses the independent physical Hill spectrum.
The actual Hill primitive has the source's convergent odd Laurent series
with the independently constructed native K's as its coefficients. The
remaining extension/uniqueness step on the entire native Sobolev domain
is not asserted by these finite-gap statements.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate ENNReal
namespace NLS.Articles.MKdVNLSHierarchies

theorem finiteGap_iff_diagonalNLS (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    miuraFiniteGap a ha ↔ realDiagonalH1Source a ha ∈
      sourceFiniteGapLocus (by simp) (by norm_num) :=
  miuraFiniteGap_iff_sourceFiniteGap a ha

theorem finiteGap_iff_mKdV_action_support (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    miuraFiniteGap a ha ↔ {n : ℕ | 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0}.Finite :=
  miuraFiniteGap_iff_action_support a ha

/-- Proposition 6 on actual finite-gap sources, with every order native
and the L² mass endpoint included. -/
theorem proposition6_finiteGap_native (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha) (m : ℕ) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (realDiagonalH1Source a ha)
        ((miuraFiniteGap_iff_sourceFiniteGap a ha).mp hf) (2*m+1) =
          2*nativeMiuraHillHamiltonian m (miuraFiniteGapSobolev a ha hf m) ∧
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (realDiagonalH1Source a ha)
        ((miuraFiniteGap_iff_sourceFiniteGap a ha).mp hf) (2*m+2) = 0 :=
  sourceFiniteGapHamiltonians_miura_native a ha hf m

/-- The convergent version of (12), with the exact factor 2 and the
physical ground-normalized Hill primitive, including exterior collapsed
gaps. No smoothness or nonzero-mean assumption is needed. -/
theorem equation12_finiteGap_native_laurent (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 < z.re → R < ‖z‖ →
      HasSum (fun k : ℕ => I*(2*nativeMiuraHillHamiltonian k (miuraFiniteGapSobolev a ha hf k)) /
        (2*z)^(2*k+1)) (canonicalMiuraHillPrimitive a (z^2)+I*z) :=
  exists_canonicalMiuraHillPrimitive_native_laurent a ha hf

end NLS.Articles.MKdVNLSHierarchies
