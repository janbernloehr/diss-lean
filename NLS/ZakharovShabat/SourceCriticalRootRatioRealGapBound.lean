import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumPath
import NLS.ZakharovShabat.SourceCriticalRootRatioVerticalLimits
import NLS.ZakharovShabat.RealGapCanonicalRootRealAxis
import NLS.ComplexAnalysis.EndpointSqrtWeight

/-! # A real-coordinate integrable bound above and below a spectral gap

The transverse estimate becomes an inverse endpoint-square-root bound
in real spectral coordinates. It controls partial horizontal integrals
uniformly as their nonzero height tends to zero.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The affine gap weight is precisely the square root of the product
of the two real endpoint distances. -/
theorem real_gap_affine_sqrt_weight (a b x : ℝ) (hab : a < b) :
    (b-a)/2 * Real.sqrt (1-((2*x-a-b)/(b-a))^2) = Real.sqrt ((x-a)*(b-x)) := by
  have hne : b-a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hδ : 0 ≤ (b-a)/2 := by positivity
  have he : (x-a)*(b-x) = ((b-a)/2)^2*(1-((2*x-a-b)/(b-a))^2) := by
    field_simp
    ring
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hδ]

/-- Inverse affine coordinates recover any real point, also after a
nonzero vertical displacement. -/
theorem sourceCanonicalRootGapPoint_inverseCoordinate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) (x : ℝ) :
    sourceCanonicalRootGapPoint hp hp1 φ n (realGapInverseCoordinate hp hp1 φ n x) = (x : ℂ) := by
  rw [sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint hp hp1 φ hφ n,
    realGapAffinePoint_inverse hp hp1 φ n hopen]

/-- Uniform domination by an integrable real endpoint weight, for
positive and negative heights simultaneously. -/
theorem exists_sourceCriticalRootRatio_realGap_domination
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧ ∀ x ∈ Ioo a b, ∀ y : ℝ, y ≠ 0 → |y| ≤ ε →
      ‖deriv (canonicalDiscriminant hp (periodOnePotential φ)) ((x : ℂ)+(y : ℂ)*I) /
        sourceCanonicalRoot hp hp1 φ ((x : ℂ)+(y : ℂ)*I)‖ ≤ M / Real.sqrt ((x-a)*(b-x)) := by
  obtain ⟨ε,M,hε,hM,hbound⟩ := exists_sourceCriticalRootRatio_transverse_weighted_bound hp hp1 φ hφ n hopen
  refine ⟨ε,M,hε,hM,?_⟩
  intro x hx y hy hyε
  have ht := realGapInverseCoordinate_mem_Ioo hp hp1 φ n hx
  have h := hbound (realGapInverseCoordinate hp hp1 φ n x) ⟨ht.1.le,ht.2.le⟩ y hy hyε
  dsimp only at h
  rw [sourceCanonicalRootGapPoint_inverseCoordinate hp hp1 φ hφ n hopen x] at h
  simp only [realGapInverseCoordinate] at h
  rw [real_gap_affine_sqrt_weight _ _ x hopen,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at h
  exact (le_div_iff₀ (Real.sqrt_pos.mpr (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)))).mpr h

/-- At a nonzero height the actual spectral quotient is continuous as
a function of the real coordinate, with no gap restriction. -/
theorem continuous_sourceCriticalRootRatio_horizontal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (y : ℝ) (hy : y ≠ 0) :
    Continuous (fun x : ℝ => deriv (canonicalDiscriminant hp (periodOnePotential φ)) ((x : ℂ)+(y : ℂ)*I) /
      sourceCanonicalRoot hp hp1 φ ((x : ℂ)+(y : ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hroot : (x : ℂ)+(y : ℂ)*I ∈ sourceCanonicalRootDomain hp hp1 φ :=
    sourceCanonicalRootDomain_of_im_ne_zero hp hp1 φ hφ _ (by simpa using hy)
  exact (sourceCriticalRootRatio_analyticOnNhd hp hp1 φ _ hroot).continuousAt.comp (f := fun t : ℝ => (t : ℂ)+(y : ℂ)*I)
    (show ContinuousAt (fun t : ℝ => (t : ℂ)+(y : ℂ)*I) x from by fun_prop)

end NLS.ZakharovShabat
