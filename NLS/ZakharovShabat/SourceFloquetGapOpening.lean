import NLS.ZakharovShabat.SourceBoundaryRootFloquetPoisson
import NLS.ZakharovShabat.SourceAngularBetaExponent
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! # A Floquet function detecting open real gaps

The squared boundary multiplier minus one vanishes at closed real gaps.
Its mixed root bracket is the negative squared multiplier, hence never
zero on real sources at exponents at least two. This supplies a local
obstruction to an open set of closed gaps.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A globally defined function which must vanish at a closed real gap. -/
def sourceFloquetGapOpening (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p) : ℂ :=
  (sourceBoundaryFloquetMultiplier hp hp1 .dirichlet n φ)^2 - 1

theorem analyticAt_sourceFloquetGapOpening_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticAt ℂ (sourceFloquetGapOpening hp hp1 n) φ :=
  ((analyticAt_sourceBoundaryFloquetMultiplier_of_realType hp hp1 .dirichlet n φ hreal).pow 2).sub analyticAt_const

theorem sourceFloquetGapOpening_eq_zero_of_closed_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    sourceFloquetGapOpening hp hp1 n φ = 0 := by
  have hz := sourceAntiDiscriminant_at_canonicalBoundaryRoot_eq_zero_of_collapsed_gap hp hp1 .dirichlet φ hreal n hgap
  have h := sourceBoundaryFloquetMultiplier_mul_reciprocal hp hp1 .dirichlet n φ
  simp only [sourceBoundaryFloquetMultiplier,sourceBoundaryTerminalAntiDiscriminant,hz,mul_zero,add_zero,sub_zero] at h ⊢
  dsimp only [sourceFloquetGapOpening,sourceBoundaryFloquetMultiplier,sourceBoundaryTerminalAntiDiscriminant]
  rw [hz,mul_zero,add_zero,pow_two,h,sub_self]

theorem sourceFloquetGapOpening_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (φ : CoeffPair p) :
    sourceFloquetGapOpening hp hp1 n φ = sourceFloquetGapOpening hq hq1 n (CoeffPair.exponentInclusion hpq φ) := by
  unfold sourceFloquetGapOpening sourceBoundaryFloquetMultiplier
    sourceBoundaryTerminalDiscriminant sourceBoundaryTerminalAntiDiscriminant
  rw [← canonicalPeriodOneBoundaryRoots_exponent hp hq hp1 hq1 hpq .dirichlet φ,
    ← sourceDiscriminant_exponent hp hq hpq φ,
    ← sourceAntiDiscriminantCandidate_exponent hp hq hp1 hq1 hpq φ]

/-- Its mixed bracket is nonzero even at a collapsed selected gap. -/
theorem sourceBracket_boundaryRoot_gapOpening
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n : ℤ) (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    sourceBracket h2p (fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
      (sourceFloquetGapOpening hp hp1 n) φ = -(sourceBoundaryFloquetMultiplier hp hp1 .dirichlet n φ)^2 := by
  have hd := (analyticAt_sourceBoundaryFloquetMultiplier_of_realType hp hp1 .dirichlet n φ hreal).differentiableAt
  have hf := (hd.hasFDerivAt.pow 2).sub_const 1
  have heq := sourceBracket_boundaryRoot_floquet_diagonal hp hp1 h2p .dirichlet φ hreal n
  unfold sourceBracket at heq ⊢
  unfold sourceFloquetGapOpening
  rw [hf.fderiv]
  simp only [map_smul,smul_eq_mul]
  norm_num only [Nat.cast_ofNat,show (2:ℕ)-1 = 1 by rfl,pow_one,nsmul_eq_mul] at *
  rw [heq]
  ring

end NLS.ZakharovShabat
