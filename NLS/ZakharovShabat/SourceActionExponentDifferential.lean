import NLS.ZakharovShabat.SourceActionRegularCotangent
import NLS.ZakharovShabat.SourceComplexActionAnalytic
import NLS.ZakharovShabat.SourceAngularBetaExponentDifferential

/-! # Exponent compatibility of actual action derivatives

The same sufficiently small midpoint circle computes the real action
at both exponents. Equality of the discriminant and canonical root
identifies its integrand. Analytic real-form uniqueness then identifies
the complex action germ and the full derivative, including closed gaps.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem sourceActionCircle_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) :
    sourceActionCircle hp hp1 ψ c R =
      sourceActionCircle hq hq1 (CoeffPair.exponentInclusion hpq ψ) c R := by
  have hΔ : canonicalDiscriminant hp (periodOnePotential ψ) =
      canonicalDiscriminant hq (periodOnePotential (CoeffPair.exponentInclusion hpq ψ)) :=
    funext (sourceDiscriminant_exponent hp hq hpq ψ)
  simp only [sourceActionCircle, sourceCriticalRootRatioJoint, hΔ,
    sourceCanonicalRoot_exponent hp hq hp1 hq1 hpq ψ]

theorem sourceRealAction_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (φ : realTypeSourceLocus p) :
    sourceRealAction hp hp1 φ.val φ.property n =
      sourceRealAction hq hq1 (CoeffPair.exponentInclusion hpq φ.val)
        (realTypeSourceExponentInclusion hpq φ).property n := by
  let χ := realTypeSourceExponentInclusion hpq φ
  let ε := sourceRealActionEpsilon hp hp1 φ.val φ.property n
  let ε' := sourceRealActionEpsilon hq hq1 χ.val χ.property n
  have hε : 0 < ε := (sourceRealActionEpsilon_spec hp hp1 φ.val φ.property n).1
  have hε' : 0 < ε' := (sourceRealActionEpsilon_spec hq hq1 χ.val χ.property n).1
  let η := min ε ε' / 2
  have hη : 0 < η := div_pos (lt_min hε hε') (by norm_num)
  have hηp : η ∈ Ioc 0 ε := ⟨hη,by dsimp [η]; linarith [min_le_left ε ε']⟩
  have hηq : η ∈ Ioc 0 ε' := ⟨hη,by dsimp [η]; linarith [min_le_right ε ε']⟩
  have hP := sourceRealAction_eq_small_midpointCircle hp hp1 φ.val φ.property n hηp
  have hQ := sourceRealAction_eq_small_midpointCircle hq hq1 χ.val χ.property n hηq
  dsimp only at hP hQ
  rw [(canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq φ.val).1,
    (canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq φ.val).2,
    sourceActionCircle_exponent hp hq hp1 hq1 hpq φ.val] at hP
  exact hP.trans hQ.symm

theorem sourceComplexAction_real_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (φ : realTypeSourceLocus p) :
    sourceComplexAction hp hp1 n φ.val =
      sourceComplexAction hq hq1 n (CoeffPair.exponentInclusion hpq φ.val) := by
  exact (sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property).trans
    ((sourceRealAction_exponent hp hq hp1 hq1 hpq n φ).trans
      (sourceComplexAction_eq_sourceRealAction hq hq1 n
        (CoeffPair.exponentInclusion hpq φ.val) (realTypeSourceExponentInclusion hpq φ).property).symm)

theorem eventually_sourceComplexAction_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (φ : realTypeSourceLocus p) :
    sourceComplexAction hp hp1 n =ᶠ[𝓝 φ.val]
      (sourceComplexAction hq hq1 n ∘ CoeffPair.exponentInclusion hpq) := by
  apply eventuallyEq_source_of_analyticAt_of_real_agreement hp φ
    (sourceComplexAction hp hp1 n) (sourceComplexAction hq hq1 n ∘ CoeffPair.exponentInclusion hpq)
    (analyticAt_sourceComplexAction_of_realType hp hp1 n φ.val φ.property)
  · exact (analyticAt_sourceComplexAction_of_realType hq hq1 n
      (CoeffPair.exponentInclusion hpq φ.val) (realTypeSourceExponentInclusion hpq φ).property).comp
        (f := CoeffPair.exponentInclusion hpq) (x := φ.val)
        ((CoeffPair.exponentInclusion hpq).analyticAt _)
  · exact sourceComplexAction_real_exponent hp hq hp1 hq1 hpq n

theorem fderiv_sourceComplexAction_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (φ : realTypeSourceLocus p) :
    fderiv ℂ (sourceComplexAction hp hp1 n) φ.val =
      (fderiv ℂ (sourceComplexAction hq hq1 n) (CoeffPair.exponentInclusion hpq φ.val)).comp
        (CoeffPair.exponentInclusion hpq) := by
  rw [(eventually_sourceComplexAction_exponent hp hq hp1 hq1 hpq n φ).fderiv_eq]
  rw [fderiv_comp φ.val (analyticAt_sourceComplexAction_of_realType hq hq1 n
    (CoeffPair.exponentInclusion hpq φ.val) (realTypeSourceExponentInclusion hpq φ).property).differentiableAt
    (CoeffPair.exponentInclusion hpq).differentiableAt, ContinuousLinearMap.fderiv]

theorem sourceActionRegularCotangent_coefficients_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (φ : realTypeSourceLocus p) :
    (sourceActionRegularCotangent hp hp1 n φ).coefficients =
      (sourceActionRegularCotangent hq hq1 n (realTypeSourceExponentInclusion hpq φ)).coefficients := by
  apply RegularSourceCotangent.coefficients_eq_of_toCotangent_eq
    (sourceActionRegularCotangent hp hp1 n φ)
    ((sourceActionRegularCotangent hq hq1 n (realTypeSourceExponentInclusion hpq φ)).restrict hpq)
  simp only [RegularSourceCotangent.restrict, sourceActionRegularCotangent_toCotangent]
  exact fderiv_sourceComplexAction_exponent hp hq hp1 hq1 hpq n φ

end NLS.ZakharovShabat
