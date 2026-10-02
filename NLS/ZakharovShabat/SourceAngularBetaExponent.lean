import NLS.ZakharovShabat.SourceAngularPrimitiveExponent
import NLS.ZakharovShabat.SourcePsiGapRootExponent
import NLS.ZakharovShabat.SourceAngularBetaSeries

/-! # Exponent compatibility of the actual beta correction

Transporting the full sets of normalized primitive values also preserves
the chosen beta value and the endpoint zero convention. For the actual
common-domain psi families, real gap-root uniqueness supplies the required
numerator agreement. Consequently every beta summand and the full
correction agree at real sources, at every finite exponent above one.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem sourceAngularDirichletTerminalIsEndpoint_exponent_iff
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (ψ : CoeffPair p) (m : ℤ) :
    SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ m ↔
      SourceAngularDirichletTerminalIsEndpoint hq hq1 (CoeffPair.exponentInclusion hpq ψ) m := by
  simp only [SourceAngularDirichletTerminalIsEndpoint,
    canonicalPeriodOneBoundaryRoots_exponent hp hq hp1 hq1 hpq .dirichlet ψ,
    (canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq ψ).1,
    (canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq ψ).2]

theorem sourceAngularBetaValues_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair q → DeletedCoeff q k) (ψ : CoeffPair p)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq ψ) : Coeff q))) :
    sourceAngularBetaValues hp hp1 n m s ψ =
      sourceAngularBetaValues hq hq1 n m t (CoeffPair.exponentInclusion hpq ψ) := by
  unfold sourceAngularBetaValues
  rw [propext (sourceAngularDirichletTerminalIsEndpoint_exponent_iff hp hq hp1 hq1 hpq ψ m),
    sourceAngularRegularDirichletValues_exponent hp hq hp1 hq1 hpq n m s t ψ hnum]

/-- Compatibility of the chosen value follows from equality of its
entire defining value set, including the endpoint convention. -/
theorem sourceAngularBeta_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair q → DeletedCoeff q k) (ψ : CoeffPair p)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq ψ) : Coeff q))) :
    sourceAngularBeta hp hp1 n m s ψ =
      sourceAngularBeta hq hq1 n m t (CoeffPair.exponentInclusion hpq ψ) := by
  unfold sourceAngularBeta
  rw [sourceAngularBetaValues_exponent hp hq hp1 hq1 hpq n m s t ψ hnum]

theorem sourceAngularBetaCorrection_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair q → DeletedCoeff q k) (ψ : CoeffPair p)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq ψ) : Coeff q))) :
    sourceAngularBetaCorrection hp hp1 n s ψ =
      sourceAngularBetaCorrection hq hq1 n t (CoeffPair.exponentInclusion hpq ψ) := by
  unfold sourceAngularBetaCorrection
  apply tsum_congr
  intro m
  simp only [sourceAngularBetaSeriesTerm,
    sourceAngularBeta_exponent hp hq hp1 hq1 hpq n m s t ψ hnum]

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
  {W : Set (CoeffPair p)} {V : Set (CoeffPair q)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}

/-- Actual common-domain psi families have identical entire numerators
at real sources; compatibility is proved from their selected gap roots. -/
theorem candidate_real_exponent_agreement
    (D : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (E : SourcePsiIsolatingComplexExtension hq hq1 V t)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceLocus p) (z : ℂ) :
    sourcePsiCandidate n (z,(s n φ.val : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq φ.val) : Coeff q)) := by
  rw [← D.real_exponent_agreement E hpq n φ]
  exact sourcePsiCandidate_exponent hpq n _ z

/-- All actual real beta values agree across exponents, with no
open-gap or regular-terminal restriction. -/
theorem beta_real_exponent_agreement
    (D : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (E : SourcePsiIsolatingComplexExtension hq hq1 V t)
    (hpq : p ≤ q) (n m : ℤ) (φ : realTypeSourceLocus p) :
    sourceAngularBeta hp hp1 n m s φ.val =
      sourceAngularBeta hq hq1 n m t (CoeffPair.exponentInclusion hpq φ.val) :=
  sourceAngularBeta_exponent hp hq hp1 hq1 hpq n m s t φ.val
    (D.candidate_real_exponent_agreement E hpq n φ)

/-- The complete off-diagonal correction agrees, including at
collapsed gaps. Each literal summand is preserved before summing. -/
theorem betaCorrection_real_exponent_agreement
    (D : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (E : SourcePsiIsolatingComplexExtension hq hq1 V t)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceLocus p) :
    sourceAngularBetaCorrection hp hp1 n s φ.val =
      sourceAngularBetaCorrection hq hq1 n t (CoeffPair.exponentInclusion hpq φ.val) :=
  sourceAngularBetaCorrection_exponent hp hq hp1 hq1 hpq n s t φ.val
    (D.candidate_real_exponent_agreement E hpq n φ)

end SourcePsiIsolatingComplexExtension
end NLS.ZakharovShabat
