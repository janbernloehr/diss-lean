import NLS.ZakharovShabat.SourceBirkhoffWeightedGradientSummability

/-! # The rectangular Birkhoff derivative errors

The sum and difference of the normalized signed coordinates give the
actual x and y derivatives. Their free Fourier functionals use exactly
the same square-root and imaginary normalizations as formula (3.2).
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The free x functional with the normalization of formula (3.2). -/
def sourceBirkhoffFreeXCotangent (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) : CoeffPair p →L[ℂ] ℂ :=
  (Real.sqrt 8 : ℂ)⁻¹ •
    (sourceGapWeightedEtaFreeCotangent hp hp1 n 1+sourceGapWeightedEtaFreeCotangent hp hp1 n (-1))

/-- The free y functional with the normalization of formula (3.2). -/
def sourceBirkhoffFreeYCotangent (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) : CoeffPair p →L[ℂ] ℂ :=
  ((Real.sqrt 8 : ℂ)*I)⁻¹ •
    (sourceGapWeightedEtaFreeCotangent hp hp1 n 1-sourceGapWeightedEtaFreeCotangent hp hp1 n (-1))

private theorem sqrt_eight_complex : (Real.sqrt 8 : ℂ) = 2*(Real.sqrt 2 : ℂ) := by
  have hr : Real.sqrt 8 = 2*Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4*2 by norm_num,Real.sqrt_mul (by norm_num)]
    rw [show (4 : ℝ) = 2^2 by norm_num,Real.sqrt_sq (by norm_num)]
  exact_mod_cast hr

/-- The free rectangular functionals have the exact signed Fourier evaluations. -/
theorem sourceBirkhoffFreeCotangents_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (h : CoeffPair p) :
    sourceBirkhoffFreeXCotangent hp hp1 n h = -(h.fst (-n)+h.snd n)/(Real.sqrt 2 : ℂ) ∧
    sourceBirkhoffFreeYCotangent hp hp1 n h = (h.fst (-n)-h.snd n)/((Real.sqrt 2 : ℂ)*I) := by
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  simp only [sourceBirkhoffFreeXCotangent,sourceBirkhoffFreeYCotangent,smul_apply,smul_eq_mul,
    add_apply,sub_apply,sourceGapWeightedEtaFreeCotangent_apply,sqrt_eight_complex]
  constructor <;> field_simp <;> ring

namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The actual rectangular derivatives are the normalized signed sum and difference. -/
theorem birkhoffXY_fderiv_eq_weighted
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W) (n : ℤ) :
    fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ.val = (Real.sqrt 8 : ℂ)⁻¹ •
      (fderiv ℂ (sourceBirkhoffWeightedCoordinate hp hp1 n s 1) φ.val+
        fderiv ℂ (sourceBirkhoffWeightedCoordinate hp hp1 n s (-1)) φ.val) ∧
    fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ.val = ((Real.sqrt 8 : ℂ)*I)⁻¹ •
      (fderiv ℂ (sourceBirkhoffWeightedCoordinate hp hp1 n s 1) φ.val-
        fderiv ℂ (sourceBirkhoffWeightedCoordinate hp hp1 n s (-1)) φ.val) := by
  obtain ⟨A,_,hφA,hξ,_⟩ := exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 φ.val φ.property
  have ha (sign : ℂ) := (analyticAt_sourceBirkhoffWeightedCoordinate hp hp1 n s sign φ.val
    (hξ n φ.val hφA) (D.gapWeightedEta_analyticAt_of_realType W hW hWB φ.val hφ φ.property n sign)
    (D.beta_series.analytic_correction n φ.val (hWB hφ))).differentiableAt.hasFDerivAt
  exact ⟨(((ha 1).add (ha (-1))).mul_const (Real.sqrt 8 : ℂ)⁻¹).fderiv,
    (((ha 1).sub (ha (-1))).mul_const ((Real.sqrt 8 : ℂ)*I)⁻¹).fderiv⟩

/-- Both actual rectangular derivative errors are outer ℓp sequences in
source operator norm at every real finite-gap source, for all finite p > 1. -/
theorem memlp_birkhoffXY_fderiv_sub_free_finiteGap
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    Memℓp (fun n : ℤ => fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ.val-sourceBirkhoffFreeXCotangent hp hp1 n) p ∧
    Memℓp (fun n : ℤ => fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ.val-sourceBirkhoffFreeYCotangent hp hp1 n) p := by
  have hplus := D.memlp_birkhoffWeighted_fderiv_sub_free_finiteGap W hW hWB φ hφ hfinite 1
  have hminus := D.memlp_birkhoffWeighted_fderiv_sub_free_finiteGap W hW hWB φ hφ hfinite (-1)
  constructor
  · convert (hplus.add hminus).const_smul (Real.sqrt 8 : ℂ)⁻¹ using 1
    funext n
    rw [(D.birkhoffXY_fderiv_eq_weighted W hW hWB φ hφ n).1]
    ext h
    simp only [sourceBirkhoffFreeXCotangent,Pi.add_apply,Pi.smul_apply,add_apply,sub_apply,smul_apply,smul_eq_mul]
    ring
  · convert (hplus.sub hminus).const_smul ((Real.sqrt 8 : ℂ)*I)⁻¹ using 1
    funext n
    rw [(D.birkhoffXY_fderiv_eq_weighted W hW hWB φ hφ n).2]
    ext h
    simp only [sourceBirkhoffFreeYCotangent,Pi.sub_apply,Pi.smul_apply,sub_apply,smul_apply,smul_eq_mul]
    ring

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
