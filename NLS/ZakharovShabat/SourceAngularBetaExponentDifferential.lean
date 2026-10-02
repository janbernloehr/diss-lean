import NLS.ZakharovShabat.SourceAngularBetaExponent
import NLS.ZakharovShabat.SourceAngularThetaTheorem13_1
import NLS.ZakharovShabat.SourceHolomorphicRealGerm

/-! # Exponent compatibility of the beta correction differential

Actual real beta agreement extends to a complex germ by the real-form
identity principle. Differentiating this germ gives the full correction
cotangent under source inclusion, even below exponent two and at
collapsed gaps. The eta contribution to theta is not addressed here.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
  {W₀ B W : Set (CoeffPair p)} {V₀ C V : Set (CoeffPair q)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}

/-- The actual correction agrees on a complex neighborhood of each
real source with the correction at any larger finite source exponent. -/
theorem eventually_betaCorrection_exponent
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (E : SourceAngularThetaCommonDomainData hq hq1 V₀ C V t)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceLocus p) :
    sourceAngularBetaCorrection hp hp1 n s =ᶠ[𝓝 φ.val]
      (sourceAngularBetaCorrection hq hq1 n t ∘ CoeffPair.exponentInclusion hpq) := by
  apply eventuallyEq_source_of_analyticAt_of_real_agreement hp φ
  · exact D.beta_series.analytic_correction n φ.val (D.source_subset (D.real_subset φ.property))
  · exact (E.beta_series.analytic_correction n (CoeffPair.exponentInclusion hpq φ.val)
      (E.source_subset (E.real_subset (realTypeSourceExponentInclusion hpq φ).property))).comp
        (f := CoeffPair.exponentInclusion hpq) (x := φ.val)
        ((CoeffPair.exponentInclusion hpq).analyticAt _)
  · intro χ
    exact D.psi.toSourcePsiIsolatingComplexExtension.betaCorrection_real_exponent_agreement
      E.psi.toSourcePsiIsolatingComplexExtension hpq n χ

/-- Equality of the full complex correction derivative, not merely
of its values on real tangent directions. No open-gap assumption is needed. -/
theorem fderiv_betaCorrection_exponent
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (E : SourceAngularThetaCommonDomainData hq hq1 V₀ C V t)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceLocus p) :
    fderiv ℂ (sourceAngularBetaCorrection hp hp1 n s) φ.val =
      (fderiv ℂ (sourceAngularBetaCorrection hq hq1 n t)
        (CoeffPair.exponentInclusion hpq φ.val)).comp (CoeffPair.exponentInclusion hpq) := by
  rw [(D.eventually_betaCorrection_exponent E hpq n φ).fderiv_eq]
  rw [fderiv_comp φ.val
    (E.beta_series.analytic_correction n (CoeffPair.exponentInclusion hpq φ.val)
      (E.source_subset (E.real_subset (realTypeSourceExponentInclusion hpq φ).property))).differentiableAt
    (CoeffPair.exponentInclusion hpq).differentiableAt, ContinuousLinearMap.fderiv]

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
