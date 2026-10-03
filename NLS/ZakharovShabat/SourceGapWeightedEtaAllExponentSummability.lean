import NLS.ZakharovShabat.SourceGapWeightedEtaFiniteGapSummability
import NLS.ZakharovShabat.SourceGradientExponentRestriction

/-! # Lemma 16.1: finite-gap eta gradient errors at every finite p > 1

Below two, coefficient inclusion places the source in the Hilbert space.
Finite-gap regularity supplies its physical H¹ representative, and
restriction of independently summable Hilbert cotangents proves G.6–G.7.
Above two, the existing physical identification applies directly. The
closed-gap identity and finite modification give the actual coordinate
estimate for the full exponent range.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A finite-gap source below two has a physical H¹ representative after
coefficient inclusion into the Hilbert space. -/
theorem sourceFiniteGap_exists_physical_hilbert_domain_below_two
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : realTypeSourceLocus p) (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ a : Domain 2, periodOnePotential (CoeffPair.exponentInclusion hp2 φ.val) = domainInclusion a := by
  have h := sourceFiniteGap_physical_mem_H1 hp hp1 φ hfinite
  let a : Domain 2 := (⟨fun n => Coeff.periodDouble φ.val.fst n,h.1⟩,
    ⟨fun n => Coeff.periodDouble φ.val.snd n,h.2⟩)
  refine ⟨a,?_⟩
  apply Prod.ext <;> ext n
  · change Coeff.periodDouble (Coeff.exponentInclusion hp2 φ.val.fst) n = scalarInclusion a.1 n
    rw [← Coeff.periodDouble_exponent,scalarInclusion_apply]
    rfl
  · change Coeff.periodDouble (Coeff.exponentInclusion hp2 φ.val.snd) n = scalarInclusion a.2 n
    rw [← Coeff.periodDouble_exponent,scalarInclusion_apply]
    rfl

/-- The closed-gap expression has a summable free-mode error at every real
finite-gap source for the full range 1 < p < ∞. -/
theorem memlp_sourceGapWeightedEtaClosedCotangent_finiteGap_all_exponents
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) (sign : ℂ) :
    Memℓp (fun n : ℤ => sourceGapWeightedEtaClosedCotangent hp hp1 n sign φ.val-
      sourceGapWeightedEtaFreeCotangent hp hp1 n sign) p := by
  rcases le_total (2 : ℝ≥0∞) p with h2p | hp2
  · exact memlp_sourceGapWeightedEtaClosedCotangent_finiteGap hp hp1 h2p φ hfinite sign
  obtain ⟨a,ha⟩ := sourceFiniteGap_exists_physical_hilbert_domain_below_two hp hp1 hp2 φ hfinite
  exact memlp_sourceGapWeightedEtaClosedCotangent_of_gradient_estimates hp hp1 φ.val φ.property
    (memlp_source_midpoint_fderiv_below_two hp hp1 hp2 φ a ha)
    (memlp_source_dirichlet_fderiv_error_below_two hp hp1 hp2 φ a ha)
    (memlp_source_antiDiscriminantCotangent_error_below_two hp hp1 hp2 φ a ha .dirichlet) sign

namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Lemma 16.1 in operator norm, at every finite source exponent strictly
above one and every real finite-gap potential in the coordinate domain. -/
theorem memlp_gapWeightedEta_fderiv_sub_free_finiteGap_all_exponents
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) (sign : ℂ) :
    Memℓp (fun n : ℤ => fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) φ.val-
      sourceGapWeightedEtaFreeCotangent hp hp1 n sign) p := by
  obtain ⟨S,hS⟩ := D.gapWeightedEta_fderiv_finiteGap_tail W hW hWB φ hφ hfinite
  apply memlp_vector_of_eq_outside_finset
    (memlp_sourceGapWeightedEtaClosedCotangent_finiteGap_all_exponents hp hp1 φ hfinite sign) S
  intro n hn
  rw [hS n hn sign]

/-- Lemma 16.1 in the physical conjugate Fourier pair norm, with the exact
signed free functional subtracted and all signed indices included. -/
theorem memlp_gapWeightedEta_conjugateGradient_sub_free_finiteGap_all_exponents
    {q : ℝ≥0∞} [Fact (1 ≤ q)] [q.HolderConjugate p]
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) (sign : ℂ) :
    Memℓp (fun n : ℤ => CoeffPair.conjugateGradient hp
      ((ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne')
      (fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) φ.val-
        sourceGapWeightedEtaFreeCotangent hp hp1 n sign)) p :=
  CoeffPair.memlp_conjugateGradient hp _ _
    (D.memlp_gapWeightedEta_fderiv_sub_free_finiteGap_all_exponents W hW hWB φ hφ hfinite sign)

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
