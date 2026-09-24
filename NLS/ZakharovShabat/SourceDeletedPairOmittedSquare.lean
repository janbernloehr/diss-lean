import NLS.ZakharovShabat.SourceStandardRootOmittedProduct
import NLS.ZakharovShabat.SourceCanonicalRootProduct
import NLS.ZakharovShabat.DiscriminantPairFactorization
import NLS.ZakharovShabat.SourceGlobalIsolation

/-!
# The deleted periodic pair is the square of the omitted standard-root product

Off every unomitted periodic gap, each standard-root factor squares to
its normalized endpoint-pair factor. The literal cutoffs and their
limits therefore identify the two deleted products, with the same
normalization at zero and nonzero indices.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal omitted standard-root cutoff squares to the deleted
periodic-pair cutoff on the moving-gap complement. -/
theorem sourceStandardRootOmittedPartialProduct_sq_eq_deletedSpectralPairPartialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (N : ℕ) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (sourceStandardRootOmittedPartialProduct hp hp1 n N (z,ψ))^2 =
      deletedSpectralPairPartialProduct
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))
        n N z := by
  have hd : singleSpectralDenominator n ^ 2 = spectralPairDenominator n := by
    by_cases hn : n = 0 <;>
      simp [singleSpectralDenominator, spectralPairDenominator, hn]
  unfold sourceStandardRootOmittedPartialProduct deletedSpectralPairPartialProduct
  rw [div_pow, ← Finset.prod_pow, hd]
  congr 1
  apply Finset.prod_congr rfl
  intro m hm
  exact sourceStandardRoot_factor_sq_eq_spectralPairFactor hp hp1 ψ m z
    (hz m (Finset.mem_erase.mp hm).1)

/-- The actual omitted product squares to the entire deleted
periodic-pair product at every point off the other gap segments. -/
theorem sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (sourceStandardRootOmittedProduct hp hp1 n ψ z)^2 =
      canonicalDeletedPeriodicProduct hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n z := by
  let ξ := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let η := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hroot := (tendsto_sourceStandardRootOmittedPartialProduct hp hp1 n ψ z).pow 2
  have hpair := (tendstoLocallyUniformlyOn_deletedSpectralPairProduct hp ξ η
    (canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ)).1.left_displacement
    (canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ)).1.right_displacement n).tendsto_at (mem_univ z)
  have hroot' : Tendsto (fun N => deletedSpectralPairPartialProduct ξ η n N z) atTop
      (𝓝 ((sourceStandardRootOmittedProduct hp hp1 n ψ z)^2)) := by
    convert hroot using 1
    funext N
    exact (sourceStandardRootOmittedPartialProduct_sq_eq_deletedSpectralPairPartialProduct
      hp hp1 ψ n N z hz).symm
  change Tendsto (fun N => deletedSpectralPairPartialProduct ξ η n N z) atTop
    (𝓝 (canonicalDeletedPeriodicProduct hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n z)) at hpair
  exact tendsto_nhds_unique hroot' hpair

/-- The deleted periodic product has no zeros on the omitted-root
standard-product domain, even at points of the selected gap. -/
theorem canonicalDeletedPeriodicProduct_ne_zero_on_sourceOmittedDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    canonicalDeletedPeriodicProduct hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n z ≠ 0 := by
  rw [← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct
    hp hp1 ψ n z hz]
  exact pow_ne_zero 2 (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n hz)

/-- On a family of disjoint source isolating discs, the deleted
periodic product is nonzero throughout every disc, including the
selected gap and either periodic endpoint. -/
theorem canonicalDeletedPeriodicProduct_ne_zero_on_sourceIsolatingDisc
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε n) :
    canonicalDeletedPeriodicProduct hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n z ≠ 0 := by
  apply canonicalDeletedPeriodicProduct_ne_zero_on_sourceOmittedDomain hp hp1 ψ n z
  intro m hmn hmseg
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N ε m (hcluster m)
  exact Set.disjoint_left.mp (hdisjoint n m (Ne.symm hmn)) hz (hseg hmseg)

end NLS.ZakharovShabat
