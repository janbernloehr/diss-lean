import NLS.ZakharovShabat.SourceBirkhoffFiniteGapFactors
import NLS.ZakharovShabat.SourceBirkhoffFixedFamilyAnalytic

/-! # The normalized signed coordinate gradient at finite-gap sources

On each closed gap the vanishing eta coordinate removes the derivatives
of the action root and beta phase. Summable multiplier errors and Lemma
16.1 therefore control the signed Birkhoff derivative; finite modification
includes all open gaps.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed free functionals have one bound at all indices. -/
theorem norm_sourceGapWeightedEtaFreeCotangent_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (sign : ℂ) (n : ℤ) :
    ‖sourceGapWeightedEtaFreeCotangent hp hp1 n sign‖ ≤ ‖sign-1‖+‖sign+1‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  rw [sourceGapWeightedEtaFreeCotangent_apply]
  have h₁ := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' h.fst (-n)).trans
    (WithLp.norm_fst_le (Coeff p) h)
  have h₂ := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' h.snd n).trans
    (WithLp.norm_snd_le (Coeff p) h)
  calc
    _ ≤ ‖(sign-1)*h.fst (-n)‖+‖(sign+1)*h.snd n‖ := norm_sub_le _ _
    _ ≤ (‖sign-1‖+‖sign+1‖)*‖h‖ := by
      rw [norm_mul,norm_mul,add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ (norm_nonneg _))
        (mul_le_mul_of_nonneg_left h₂ (norm_nonneg _))

namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The exact product-rule simplification at a real closed gap. -/
theorem birkhoffWeighted_fderiv_closed
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0)
    (sign : ℂ) :
    fderiv ℂ (sourceBirkhoffWeightedCoordinate hp hp1 n s sign) φ.val =
      (sourceNormalizedActionRoot hp hp1 n φ.val*exp (sign*I*sourceAngularBetaCorrection hp hp1 n s φ.val)) •
        fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) φ.val := by
  obtain ⟨A,_,hφA,hξ,_⟩ := exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 φ.val φ.property
  have hz := D.gapWeightedEta_analyticAt_of_realType W hW hWB φ.val hφ φ.property n sign
  have he : AnalyticAt ℂ (fun ψ => exp (sign*I*sourceAngularBetaCorrection hp hp1 n s ψ)) φ.val :=
    (analyticAt_const.mul (D.beta_series.analytic_correction n φ.val (hWB hφ))).cexp'
  have hd := (((hξ n φ.val hφA).differentiableAt.hasFDerivAt.fun_mul
    hz.differentiableAt.hasFDerivAt).fun_mul he.differentiableAt.hasFDerivAt).fderiv
  have hzero := sourceGapWeightedEtaCoordinate_eq_zero_of_real_collapsed_gap hp hp1 n s φ.val φ.property
    (canonicalPeriodOneBoundaryRoot_mem_omittedDomain hp hp1 .dirichlet φ.val φ.property n) hgap sign
  change fderiv ℂ (sourceBirkhoffWeightedCoordinate hp hp1 n s sign) φ.val = _ at hd
  rw [hd]
  ext h
  simp only [add_apply,smul_apply,smul_eq_mul,hzero,mul_zero,zero_mul,zero_add,add_zero]
  ring

/-- The actual signed Birkhoff derivative has a summable free Fourier error
at every real finite-gap source, for every finite p > 1. -/
theorem memlp_birkhoffWeighted_fderiv_sub_free_finiteGap
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) (sign : ℂ) :
    Memℓp (fun n : ℤ => fderiv ℂ (sourceBirkhoffWeightedCoordinate hp hp1 n s sign) φ.val-
      sourceGapWeightedEtaFreeCotangent hp hp1 n sign) p := by
  let c (n : ℤ) := sourceNormalizedActionRoot hp hp1 n φ.val*
    exp (sign*I*sourceAngularBetaCorrection hp hp1 n s φ.val)
  have hc : Memℓp (fun n => c n-1) p := D.memlp_birkhoffFactor_sub_one_finiteGap φ (hWB hφ) hfinite sign
  obtain ⟨C,_,hC⟩ := exists_norm_bound_of_memlp_sub_one hc
  have hη := D.memlp_gapWeightedEta_fderiv_sub_free_finiteGap_all_exponents W hW hWB φ hφ hfinite sign
  have h₁ := memlp_smul_of_bounded_scalar c _ hη C hC
  have h₂ := memlp_smul_of_bounded_vector _ (fun n => sourceGapWeightedEtaFreeCotangent hp hp1 n sign)
    hc (‖sign-1‖+‖sign+1‖) (norm_sourceGapWeightedEtaFreeCotangent_le hp hp1 sign)
  apply memlp_vector_of_eq_outside_finset (h₁.add h₂) hfinite.toFinset
  intro n hn
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
    by_contra hg
    exact hn (hfinite.mem_toFinset.mpr hg)
  rw [D.birkhoffWeighted_fderiv_closed W hW hWB φ hφ n hgap sign]
  ext h
  simp only [Pi.add_apply,add_apply,sub_apply,smul_apply,smul_eq_mul,c]
  ring

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
