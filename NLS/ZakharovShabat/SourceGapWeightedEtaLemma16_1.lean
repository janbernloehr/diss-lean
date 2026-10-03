import NLS.ZakharovShabat.SourceGapWeightedEtaAllExponentSummability
import NLS.ZakharovShabat.SourceBirkhoffMapAnalytic

/-! # The explicit Fourier-mode form of Lemma 16.1

The source convention reads opposite indices in the two components.
Recovering the physical gradient reverses these indices once more: eta
sign +1 has free gradient -2 times the second component at -n, and sign
-1 has free gradient -2 times the first component at n. The actual
constructed Birkhoff family satisfies both estimates for every finite p > 1.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- The exact signed free Fourier gradient in the physical coefficient convention. -/
theorem conjugateGradient_sourceGapWeightedEtaFreeCotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (n : ℤ) (sign : ℂ) :
    CoeffPair.conjugateGradient hp hq (sourceGapWeightedEtaFreeCotangent hp hp1 n sign) =
      (sign-1) • CoeffPair.inlCLM (lp.single q n 1)-
        (sign+1) • CoeffPair.inrCLM (lp.single q (-n) 1) := by
  apply (CoeffPair.toMax q).injective
  apply Prod.ext
  · ext k
    change (CoeffPair.conjugateGradient hp hq (sourceGapWeightedEtaFreeCotangent hp hp1 n sign)).fst k =
      (sign-1)*(lp.single q n (1 : ℂ) : Coeff q) k-(sign+1)*0
    simp [sourceGapWeightedEtaFreeCotangent_apply,lp.single_apply,Pi.single_apply,eq_comm]
  · ext k
    change (CoeffPair.conjugateGradient hp hq (sourceGapWeightedEtaFreeCotangent hp hp1 n sign)).snd k =
      (sign-1)*0-(sign+1)*(lp.single q (-n) (1 : ℂ) : Coeff q) k
    by_cases hk : k = -n
    · subst k
      simp [lp.single_apply]
    · have hn : n ≠ -k := by omega
      simp [lp.single_apply,hk,hn]

namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The entire actual gradient differs from the explicit free pair by an
outer ℓp sequence in the physical conjugate norm. -/
theorem memlp_gapWeightedEta_explicit_gradient_error_finiteGap
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s) (hq : q ≠ ⊤)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) (sign : ℂ) :
    Memℓp (fun n : ℤ => CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) φ.val)-
      ((sign-1) • CoeffPair.inlCLM (lp.single q n 1)-
        (sign+1) • CoeffPair.inrCLM (lp.single q (-n) 1))) p := by
  have h := D.memlp_gapWeightedEta_conjugateGradient_sub_free_finiteGap_all_exponents
    (q := q) W hW hWB φ hφ hfinite sign
  convert h using 1
  funext n
  rw [← conjugateGradient_sourceGapWeightedEtaFreeCotangent hp hp1 hq n sign]
  exact (map_sub (CoeffPair.conjugateGradientCLM hp hq) _ _).symm

/-- Lemma 16.1: both signed gradient errors have ℓp conjugate-pair norms,
including all open gaps and every tail index, at every real finite-gap source. -/
theorem gapWeightedEta_lemma16_1
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s) (hq : q ≠ ⊤)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    Memℓp (fun n : ℤ => ‖CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s 1) φ.val)+
      (2 : ℂ) • CoeffPair.inrCLM (lp.single q (-n) 1)‖) p ∧
    Memℓp (fun n : ℤ => ‖CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s (-1)) φ.val)+
      (2 : ℂ) • CoeffPair.inlCLM (lp.single q n 1)‖) p := by
  constructor
  · simpa [show (1 : ℂ)+1 = 2 by norm_num] using
      (D.memlp_gapWeightedEta_explicit_gradient_error_finiteGap hq W hW hWB φ hφ hfinite 1).norm
  · simpa [show (-1 : ℂ)-1 = -2 by norm_num] using
      (D.memlp_gapWeightedEta_explicit_gradient_error_finiteGap hq W hW hWB φ hφ hfinite (-1)).norm

end SourceAngularEtaLocalCommonDomainData

/-- One constructed Birkhoff family satisfies the full explicit Lemma 16.1
at every real finite-gap source, for every finite source exponent above one. -/
theorem exists_sourceBirkhoffFamily_lemma16_1
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
      SourceBirkhoffMapComplexData hp hp1 W₀ B W s ∧
      ∀ φ : realTypeSourceSubmodule p, φ ∈ sourceFiniteGapLocus hp hp1 →
        Memℓp (fun n : ℤ => ‖CoeffPair.conjugateGradient hp hq
          (fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s 1) φ.val)+
          (2 : ℂ) • CoeffPair.inrCLM (lp.single q (-n) 1)‖) p ∧
        Memℓp (fun n : ℤ => ‖CoeffPair.conjugateGradient hp hq
          (fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s (-1)) φ.val)+
          (2 : ℂ) • CoeffPair.inlCLM (lp.single q n 1)‖) p := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W₀,B,W,s,D,fun φ hfinite => D.angular.gapWeightedEta_lemma16_1 hq
    W D.source_open D.source_subset φ (D.real_subset φ.property) hfinite⟩

end NLS.ZakharovShabat
