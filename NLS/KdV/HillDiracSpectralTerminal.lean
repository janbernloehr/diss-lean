import NLS.KdV.HillDiracTerminalSheet
import NLS.KdV.HillSpectralCoreSequence
import NLS.ZakharovShabat.SourceStandardRootPhase
import NLS.ZakharovShabat.SourceBirkhoffSpectralTerminal

/-! Exact identification of the actual Hill spectral polynomials with
the literal Dirac spectral terminal at the phase-rotated SAME source.
The physical sheet sign fixes rootCoeff=i*sineNumerator. Both signs
hold at complex collapsed gaps without dividing by a gap or action. -/
noncomputable section
open Complex NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

theorem physicalDirichletRootCoefficient_eq_rotatedSineNumerator (P : HillProductEquationPatch)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    P.physicalDirichletRootCoefficient n q = I*sourceDirichletEtaSineNumerator
      (by simp) (by norm_num) ((n:ℕ):ℤ) (sourcePhase (P.sourcePsi q)) := by
  unfold physicalDirichletRootCoefficient abelianGapRootMultiplier
  rw [P.physicalDirichletSheet_eq_rotatedAntiDiscriminant n q hq]
  unfold sourceDirichletEtaSineNumerator
  rw [← P.physicalDirichletFrequency_eq_rotatedDirichlet q ((n:ℕ):ℤ)]
  dsimp only
  rw [sourceStandardRootOmittedProduct_sourcePhase]
  let A := sourceAntiDiscriminantCandidate (by simp) (by norm_num) (sourcePhase (P.sourcePsi q))
    (P.physicalDirichletFrequency ((n:ℕ):ℤ) q)
  let O := sourceStandardRootOmittedProduct (by simp) (by norm_num) ((n:ℕ):ℤ) (P.sourcePsi q)
    (P.physicalDirichletFrequency ((n:ℕ):ℤ) q)
  change -A/(2*I*O)=I*(A/(2*O))
  by_cases hO : O=0
  · simp only [hO,mul_zero,div_zero]
  · field_simp [hO]
    simp only [I_sq]
    ring

theorem physicalSpectralFactorMinus_eq_rotatedTerminal (P : HillProductEquationPatch)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    P.physicalSpectralFactorMinus n q =
      2*sourceStandardRootMidpoint (by simp) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*
        sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) ((n:ℕ):ℤ) 1 (sourcePhase (P.sourcePsi q)) := by
  unfold physicalSpectralFactorMinus sourceGapWeightedEtaTerminalCoordinate
  rw [P.physicalDirichletRootCoefficient_eq_rotatedSineNumerator n q hq,
    ← P.physicalDirichletFrequency_eq_rotatedDirichlet q ((n:ℕ):ℤ),canonicalPeriodicMidpoint_sourcePhase]
  simp only [one_mul]
  ring

theorem physicalSpectralFactorPlus_eq_rotatedTerminal (P : HillProductEquationPatch)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    P.physicalSpectralFactorPlus n q =
      2*sourceStandardRootMidpoint (by simp) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*
        sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) ((n:ℕ):ℤ) (-1) (sourcePhase (P.sourcePsi q)) := by
  unfold physicalSpectralFactorPlus sourceGapWeightedEtaTerminalCoordinate
  rw [P.physicalDirichletRootCoefficient_eq_rotatedSineNumerator n q hq,
    ← P.physicalDirichletFrequency_eq_rotatedDirichlet q ((n:ℕ):ℤ),canonicalPeriodicMidpoint_sourcePhase]
  simp only [neg_mul]
  ring

end NLS.KdV.HillProductEquationPatch
