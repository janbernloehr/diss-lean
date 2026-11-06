import NLS.ZakharovShabat.SourceBirkhoffCoordinateExponent

/-! # Exact actual gap-weighted eta agreement across exponents

The literal terminal numerator and chart-independent annular remainder
identify both signed eta coordinates, including every collapsed gap.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1≤p)] [Fact (1≤q)]
namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p≠⊤} {hq : q≠⊤} {hp1 : 1<p} {hq1 : 1<q}
  {W₀ B : Set (CoeffPair p)} {V₀ C : Set (CoeffPair q)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {t : (k : ℤ) → CoeffPair q → DeletedCoeff q k}

theorem gapWeightedEta_real_exponent
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (E : SourceAngularEtaLocalCommonDomainData hq hq1 V₀ C t)
    (W : Set (CoeffPair p)) (V : Set (CoeffPair q))
    (hW : IsOpen W) (hV : IsOpen V) (hWB : W⊆B) (hVC : V⊆C)
    (hpq : p≤q) (n : ℤ) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val∈W) (hφ' : CoeffPair.exponentInclusion hpq φ.val∈V) (sign : ℂ) :
    sourceGapWeightedEtaCoordinate hp hp1 n s sign φ.val=
      sourceGapWeightedEtaCoordinate hq hq1 n t sign (CoeffPair.exponentInclusion hpq φ.val) := by
  have hrem := D.etaRemainder_real_exponent E W V hW hV hWB hVC hpq n φ hφ hφ'
  have hμ := canonicalPeriodOneBoundaryRoots_exponent hp hq hp1 hq1 hpq .dirichlet φ.val
  have hsin : sourceDirichletEtaSineNumerator hp hp1 n φ.val=
      sourceDirichletEtaSineNumerator hq hq1 n (CoeffPair.exponentInclusion hpq φ.val) := by
    dsimp only [sourceDirichletEtaSineNumerator]
    rw [←hμ,←sourceAntiDiscriminantCandidate_exponent hp hq hp1 hq1 hpq φ.val,
      ←sourceStandardRootOmittedProduct_exponent hp hq hp1 hq1 hpq n φ.val]
  simp only [sourceGapWeightedEtaCoordinate,hrem,hμ,hsin,
    canonicalPeriodicMidpoint_source_exponent hp hq hp1 hq1 hpq φ.val n]

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
