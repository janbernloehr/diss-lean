import NLS.ComplexAnalysis.MovingSpectralParameter
import NLS.ZakharovShabat.SourceBoundaryRootDifferential
import NLS.ZakharovShabat.SourceAntiDiscriminantPoissonGradient

/-! # Actual moving boundary-terminal data and Floquet multipliers

Both the source and spectral arguments move in these functionals. Their
full cotangents follow from the actual joint families and canonical root
analyticity. The original unimodular identity gives the nonzero signed
Floquet multiplier, including at collapsed gaps.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceBoundaryTerminalDiscriminant (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p) : ℂ :=
  canonicalDiscriminant hp (periodOnePotential φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)

def sourceBoundaryTerminalAntiDiscriminant (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p) : ℂ :=
  sourceAntiDiscriminantCandidate hp hp1 φ (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)

/-- The boundary sign selects the multiplier of the original ordinary
boundary solution: `(Delta+delta)/2` for Dirichlet and `(Delta-delta)/2`
for Neumann. -/
def sourceBoundaryFloquetMultiplier (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p) : ℂ :=
  (sourceBoundaryTerminalDiscriminant hp hp1 b n φ+
    extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ)/2

theorem analyticAt_sourceBoundaryTerminalDiscriminant_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticAt ℂ (sourceBoundaryTerminalDiscriminant hp hp1 b n) φ := by
  simpa only [sourceBoundaryTerminalDiscriminant,Function.comp_def] using!
    (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
    (canonicalPeriodOneBoundaryRoots hp hp1 b φ n,φ) (mem_univ _)).comp
    (f := fun ψ : CoeffPair p => (canonicalPeriodOneBoundaryRoots hp hp1 b ψ n,ψ))
    ((analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 b φ hreal n).prod analyticAt_id)

theorem analyticAt_sourceBoundaryTerminalAntiDiscriminant_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticAt ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 b n) φ := by
  simpa only [sourceBoundaryTerminalAntiDiscriminant,Function.comp_def] using!
    (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1
    (canonicalPeriodOneBoundaryRoots hp hp1 b φ n,φ) (mem_univ _)).comp
    (f := fun ψ : CoeffPair p => (canonicalPeriodOneBoundaryRoots hp hp1 b ψ n,ψ))
    ((analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 b φ hreal n).prod analyticAt_id)

theorem analyticAt_sourceBoundaryFloquetMultiplier_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticAt ℂ (sourceBoundaryFloquetMultiplier hp hp1 b n) φ :=
  ((analyticAt_sourceBoundaryTerminalDiscriminant_of_realType hp hp1 b n φ hreal).add
    (analyticAt_const.mul
      (analyticAt_sourceBoundaryTerminalAntiDiscriminant_of_realType hp hp1 b n φ hreal))).div_const

/-- The moving discriminant cotangent includes the actual root derivative. -/
theorem fderiv_sourceBoundaryTerminalDiscriminant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    fderiv ℂ (sourceBoundaryTerminalDiscriminant hp hp1 b n) φ =
      sourceDiscriminantCotangent hp μ φ+
        deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ •
          fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ := by
  exact NLS.ComplexAnalysis.fderiv_moving_spectral_parameter
    (fun t : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential t.2) t.1)
    (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ
    (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 _ (mem_univ _)).differentiableAt
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 b φ hreal n).differentiableAt

/-- The moving anti-discriminant has both fixed-source and spectral terms,
even when its value is zero at a collapsed gap. -/
theorem fderiv_sourceBoundaryTerminalAntiDiscriminant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 b n) φ =
      sourceAntiDiscriminantCotangent hp hp1 μ φ+
        deriv (sourceAntiDiscriminantCandidate hp hp1 φ) μ •
          fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ := by
  exact NLS.ComplexAnalysis.fderiv_moving_spectral_parameter
    (fun t : ℂ × CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 t.2 t.1)
    (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ
    (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1 _ (mem_univ _)).differentiableAt
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 b φ hreal n).differentiableAt

/-- The signed boundary multiplier and its algebraic reciprocal multiply
to one at every complex source. Simplicity and real type are unnecessary. -/
theorem sourceBoundaryFloquetMultiplier_mul_reciprocal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p) :
    sourceBoundaryFloquetMultiplier hp hp1 b n φ*
      ((sourceBoundaryTerminalDiscriminant hp hp1 b n φ-
        extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ)/2) = 1 := by
  have hs := sourceDiscriminant_sq_sub_four_at_canonicalBoundaryRoot hp hp1 b φ n
  cases b <;> simp only [sourceBoundaryFloquetMultiplier,sourceBoundaryTerminalDiscriminant,
    sourceBoundaryTerminalAntiDiscriminant,extensionSign] at * <;>
    linear_combination (1/4 : ℂ)*hs

/-- The actual multiplier never vanishes, including at collapsed gaps. -/
theorem sourceBoundaryFloquetMultiplier_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p) :
    sourceBoundaryFloquetMultiplier hp hp1 b n φ ≠ 0 := by
  intro hz
  have h := sourceBoundaryFloquetMultiplier_mul_reciprocal hp hp1 b n φ
  rw [hz,zero_mul] at h
  exact zero_ne_one h

/-- This is the original characteristic polynomial of the period-one
monodromy, with the actual terminal discriminant as trace. -/
theorem sourceBoundaryFloquetMultiplier_characteristic_polynomial
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p) :
    (sourceBoundaryFloquetMultiplier hp hp1 b n φ)^2-
      sourceBoundaryTerminalDiscriminant hp hp1 b n φ*sourceBoundaryFloquetMultiplier hp hp1 b n φ+1 = 0 := by
  have hs := sourceDiscriminant_sq_sub_four_at_canonicalBoundaryRoot hp hp1 b φ n
  cases b <;> simp only [sourceBoundaryFloquetMultiplier,sourceBoundaryTerminalDiscriminant,
    sourceBoundaryTerminalAntiDiscriminant,extensionSign] at * <;>
    linear_combination -(1/4 : ℂ)*hs

end NLS.ZakharovShabat
