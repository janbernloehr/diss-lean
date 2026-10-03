import NLS.ZakharovShabat.SourceGapWeightedEtaClosedSummability
import NLS.ZakharovShabat.SourceFiniteGapHilbertRealization
import NLS.SequenceSpaces.SourceConjugateGradient

/-! # Finite-gap coordinate gradient errors for finite p ≥ 2

Finite-gap regularity supplies the physical H¹ hypothesis. Outside the
finitely many open gaps, the genuine coordinate derivative equals the
closed-gap spectral expression. Finite modification then gives the whole
signed sequence in operator norm and in the conjugate Fourier pair norm.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The closed-gap expression has a summable free-mode error at every real
finite-gap source; no additional H¹ representative is assumed. -/
theorem memlp_sourceGapWeightedEtaClosedCotangent_finiteGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : realTypeSourceLocus p) (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) (sign : ℂ) :
    Memℓp (fun n : ℤ => sourceGapWeightedEtaClosedCotangent hp hp1 n sign φ.val-
      sourceGapWeightedEtaFreeCotangent hp hp1 n sign) p := by
  obtain ⟨ψ,he,hr,a,ha⟩ := sourceFiniteGap_exists_hilbert_realization hp hp1 h2p φ hfinite
  have h := memlp_sourceGapWeightedEtaClosedCotangent_sub_free hp hp1 h2p ψ hr a ha sign
  simpa only [he] using h

namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The actual coordinate derivative differs from the exact free Fourier
functional by an ℓp sequence in operator norm, including every open gap. -/
theorem memlp_gapWeightedEta_fderiv_sub_free_finiteGap
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) (sign : ℂ) :
    Memℓp (fun n : ℤ => fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) φ.val-
      sourceGapWeightedEtaFreeCotangent hp hp1 n sign) p := by
  obtain ⟨S,hS⟩ := D.gapWeightedEta_fderiv_finiteGap_tail W hW hWB φ hφ hfinite
  apply memlp_vector_of_eq_outside_finset
    (memlp_sourceGapWeightedEtaClosedCotangent_finiteGap hp hp1 h2p φ hfinite sign) S
  intro n hn
  rw [hS n hn sign]

/-- The same genuine finite-gap derivative error has an outer ℓp sequence
of physical conjugate Fourier gradients, in the full pair norm. -/
theorem memlp_gapWeightedEta_conjugateGradient_sub_free_finiteGap
    {q : ℝ≥0∞} [Fact (1 ≤ q)] [q.HolderConjugate p]
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) (sign : ℂ) :
    Memℓp (fun n : ℤ => CoeffPair.conjugateGradient hp
      ((ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne')
      (fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) φ.val-
        sourceGapWeightedEtaFreeCotangent hp hp1 n sign)) p :=
  CoeffPair.memlp_conjugateGradient hp _ _
    (D.memlp_gapWeightedEta_fderiv_sub_free_finiteGap h2p W hW hWB φ hφ hfinite sign)

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
