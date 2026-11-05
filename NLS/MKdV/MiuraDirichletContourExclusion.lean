import NLS.MKdV.MiuraDirichletRootIdentification
import NLS.ZakharovShabat.SourceCanonicalRootRealBand

/-! # Actual independent Dirichlet energies are excluded from action contours

The rotated source roots retain the original periodic-gap indices. The
source root domain therefore excludes both square roots of every actual
positive Hill Dirichlet energy, including closed gaps.
-/
noncomputable section
open Set Complex
open NLS.ZakharovShabat NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraRotatedDirichletRoots_mem_periodicSegment (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℤ) :
    miuraRotatedDirichletRoots a m ∈ sourcePeriodicSegment (by simp) (by norm_num)
      (sobolevSourceInclusion (a,a)) m := by
  have h := sourcePeriodicSegment_mem_of_realIcc (by simp) (by norm_num)
    (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property m
    (miuraRotatedDirichletRoots a m).re (miuraRotatedDirichletRoots_mem_gap a ha m)
  have he : ((miuraRotatedDirichletRoots a m).re : ℂ) = miuraRotatedDirichletRoots a m := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using (miuraRotatedDirichletRoots_real a ha m).symm
  rwa [he] at h

theorem miuraDirichletEnergy_ne_sq_on_rootDomain (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (sobolevSourceInclusion (a,a))) :
    z^2 ≠ (hillDirichletEnergy (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1
      (realSobolevMiuraHillPotential a ha).property.2 m hm : ℂ) := by
  intro he
  rw [← miuraRotatedDirichletRoots_sq a ha m hm] at he
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · exact hz m (he ▸ miuraRotatedDirichletRoots_mem_periodicSegment a ha m)
  · apply hz (-(m : ℤ))
    rw [he,← miuraRotatedDirichletRoots_neg_nat a ha m hm]
    exact miuraRotatedDirichletRoots_mem_periodicSegment a ha (-(m : ℤ))

end NLS.MKdV
