import NLS.ZakharovShabat.SourceBirkhoffRectangularGradientSummability

/-! # Lemma 16.2: the rectangular Fourier-gradient errors

The actual rectangular gradients differ from the explicit free Fourier
pairs by sequences with ℓp conjugate-pair norms at every real finite-gap
source and every finite source exponent strictly above one.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The physical free x gradient, in the period-one source convention. -/
def sourceBirkhoffFreeXGradient (q : ℝ≥0∞) [Fact (1 ≤ q)] (n : ℤ) : CoeffPair q :=
  (-(Real.sqrt 2 : ℂ)⁻¹) •
    (CoeffPair.inlCLM (lp.single q n 1)+CoeffPair.inrCLM (lp.single q (-n) 1))

/-- The physical free y gradient, including the imaginary normalization. -/
def sourceBirkhoffFreeYGradient (q : ℝ≥0∞) [Fact (1 ≤ q)] (n : ℤ) : CoeffPair q :=
  ((Real.sqrt 2 : ℂ)*I)⁻¹ •
    (CoeffPair.inlCLM (lp.single q n 1)-CoeffPair.inrCLM (lp.single q (-n) 1))

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Conjugate-gradient recovery gives exactly the two free Fourier pairs. -/
theorem conjugateGradient_sourceBirkhoffFreeCotangents
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (n : ℤ) :
    CoeffPair.conjugateGradient hp hq (sourceBirkhoffFreeXCotangent hp hp1 n) = sourceBirkhoffFreeXGradient q n ∧
    CoeffPair.conjugateGradient hp hq (sourceBirkhoffFreeYCotangent hp hp1 n) = sourceBirkhoffFreeYGradient q n := by
  constructor
  · apply (CoeffPair.toMax q).injective
    apply Prod.ext
    · ext k
      change (CoeffPair.conjugateGradient hp hq (sourceBirkhoffFreeXCotangent hp hp1 n)).fst k =
        -(Real.sqrt 2 : ℂ)⁻¹*((lp.single q n (1 : ℂ) : Coeff q) k+0)
      rw [CoeffPair.conjugateGradient_fst,(sourceBirkhoffFreeCotangents_apply hp hp1 n _).1]
      simp [lp.single_apply,Pi.single_apply,div_eq_mul_inv,eq_comm]
      split_ifs <;> simp
    · ext k
      change (CoeffPair.conjugateGradient hp hq (sourceBirkhoffFreeXCotangent hp hp1 n)).snd k =
        -(Real.sqrt 2 : ℂ)⁻¹*(0+(lp.single q (-n) (1 : ℂ) : Coeff q) k)
      rw [CoeffPair.conjugateGradient_snd,(sourceBirkhoffFreeCotangents_apply hp hp1 n _).1]
      by_cases hk : k = -n
      · subst k
        simp [lp.single_apply,div_eq_mul_inv]
      · have hn : n ≠ -k := by omega
        simp [lp.single_apply,hk,hn]
  · apply (CoeffPair.toMax q).injective
    apply Prod.ext
    · ext k
      change (CoeffPair.conjugateGradient hp hq (sourceBirkhoffFreeYCotangent hp hp1 n)).fst k =
        ((Real.sqrt 2 : ℂ)*I)⁻¹*((lp.single q n (1 : ℂ) : Coeff q) k-0)
      rw [CoeffPair.conjugateGradient_fst,(sourceBirkhoffFreeCotangents_apply hp hp1 n _).2]
      simp [lp.single_apply,Pi.single_apply,div_eq_mul_inv,eq_comm]
      split_ifs <;> simp
    · ext k
      change (CoeffPair.conjugateGradient hp hq (sourceBirkhoffFreeYCotangent hp hp1 n)).snd k =
        ((Real.sqrt 2 : ℂ)*I)⁻¹*(0-(lp.single q (-n) (1 : ℂ) : Coeff q) k)
      rw [CoeffPair.conjugateGradient_snd,(sourceBirkhoffFreeCotangents_apply hp hp1 n _).2]
      by_cases hk : k = -n
      · subst k
        simp [lp.single_apply,div_eq_mul_inv]
      · have hn : n ≠ -k := by omega
        simp [lp.single_apply,hk,hn]

namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Lemma 16.2 for both actual rectangular coordinates, with the explicit
free Fourier gradients and every signed index included. -/
theorem birkhoff_lemma16_2
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s) (hq : q ≠ ⊤)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    Memℓp (fun n : ℤ => ‖CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ.val)-sourceBirkhoffFreeXGradient q n‖) p ∧
    Memℓp (fun n : ℤ => ‖CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ.val)-sourceBirkhoffFreeYGradient q n‖) p := by
  have h := D.memlp_birkhoffXY_fderiv_sub_free_finiteGap W hW hWB φ hφ hfinite
  constructor
  · have hx := (CoeffPair.memlp_conjugateGradient hp hq _ h.1).norm
    convert hx using 1
    funext n
    rw [← (conjugateGradient_sourceBirkhoffFreeCotangents hp hp1 hq n).1]
    congr 1
    exact (map_sub (CoeffPair.conjugateGradientCLM hp hq) _ _).symm
  · have hy := (CoeffPair.memlp_conjugateGradient hp hq _ h.2).norm
    convert hy using 1
    funext n
    rw [← (conjugateGradient_sourceBirkhoffFreeCotangents hp hp1 hq n).2]
    congr 1
    exact (map_sub (CoeffPair.conjugateGradientCLM hp hq) _ _).symm

end SourceAngularEtaLocalCommonDomainData

/-- A constructed Birkhoff family satisfies the full Lemma 16.2 at every
real finite-gap source for every finite source exponent strictly above one. -/
theorem exists_sourceBirkhoffFamily_lemma16_2
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
      SourceBirkhoffMapComplexData hp hp1 W₀ B W s ∧
      ∀ φ : realTypeSourceSubmodule p, φ ∈ sourceFiniteGapLocus hp hp1 →
        Memℓp (fun n : ℤ => ‖CoeffPair.conjugateGradient hp hq
          (fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ.val)-sourceBirkhoffFreeXGradient q n‖) p ∧
        Memℓp (fun n : ℤ => ‖CoeffPair.conjugateGradient hp hq
          (fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ.val)-sourceBirkhoffFreeYGradient q n‖) p := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W₀,B,W,s,D,fun φ hfinite => D.angular.birkhoff_lemma16_2 hq
    W D.source_open D.source_subset φ (D.real_subset φ.property) hfinite⟩

end NLS.ZakharovShabat
