import NLS.ZakharovShabat.SourceBoundaryFloquetCommutation

/-! # Exponent compatibility of moving boundary differentials

The actual signed boundary roots and moving Floquet multipliers agree
under source exponent inclusion. Differentiating these identities at
real sources preserves the full moving cotangents, not just their
fixed-spectral-parameter parts.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Coefficient-preserving inclusion of the real source loci. -/
def realTypeSourceExponentInclusion (hpq : p ≤ q) (φ : realTypeSourceLocus p) :
    realTypeSourceLocus q :=
  ⟨CoeffPair.exponentInclusion hpq φ.val, fun n => φ.property n⟩

theorem sourceBoundaryFloquetMultiplier_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p) :
    sourceBoundaryFloquetMultiplier hp hp1 b n φ =
      sourceBoundaryFloquetMultiplier hq hq1 b n (CoeffPair.exponentInclusion hpq φ) := by
  unfold sourceBoundaryFloquetMultiplier sourceBoundaryTerminalDiscriminant
    sourceBoundaryTerminalAntiDiscriminant
  rw [sourceDiscriminant_exponent hp hq hpq,
    sourceAntiDiscriminantCandidate_exponent hp hq hp1 hq1 hpq,
    canonicalPeriodOneBoundaryRoots_exponent hp hq hp1 hq1 hpq]

theorem fderiv_canonicalPeriodOneBoundaryRoots_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (b : BoundaryCondition) (n : ℤ) (φ : realTypeSourceLocus p) :
    fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ.val =
      (fderiv ℂ (fun ψ : CoeffPair q => canonicalPeriodOneBoundaryRoots hq hq1 b ψ n)
        (CoeffPair.exponentInclusion hpq φ.val)).comp (CoeffPair.exponentInclusion hpq) := by
  have heq : (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) =
      (fun ψ : CoeffPair q => canonicalPeriodOneBoundaryRoots hq hq1 b ψ n) ∘
        CoeffPair.exponentInclusion hpq := by
    funext ψ
    exact congrFun (canonicalPeriodOneBoundaryRoots_exponent hp hq hp1 hq1 hpq b ψ) n
  rw [heq, fderiv_comp φ.val
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hq hq1 b _
      (realTypeSourceExponentInclusion hpq φ).property n).differentiableAt
    (CoeffPair.exponentInclusion hpq).differentiableAt, ContinuousLinearMap.fderiv]

theorem fderiv_sourceBoundaryFloquetMultiplier_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (b : BoundaryCondition) (n : ℤ) (φ : realTypeSourceLocus p) :
    fderiv ℂ (sourceBoundaryFloquetMultiplier hp hp1 b n) φ.val =
      (fderiv ℂ (sourceBoundaryFloquetMultiplier hq hq1 b n)
        (CoeffPair.exponentInclusion hpq φ.val)).comp (CoeffPair.exponentInclusion hpq) := by
  have heq : sourceBoundaryFloquetMultiplier hp hp1 b n =
      sourceBoundaryFloquetMultiplier hq hq1 b n ∘ CoeffPair.exponentInclusion hpq := by
    funext ψ
    exact sourceBoundaryFloquetMultiplier_exponent hp hq hp1 hq1 hpq b n ψ
  rw [heq, fderiv_comp φ.val
    (analyticAt_sourceBoundaryFloquetMultiplier_of_realType hq hq1 b n _
      (realTypeSourceExponentInclusion hpq φ).property).differentiableAt
    (CoeffPair.exponentInclusion hpq).differentiableAt, ContinuousLinearMap.fderiv]

end NLS.ZakharovShabat
