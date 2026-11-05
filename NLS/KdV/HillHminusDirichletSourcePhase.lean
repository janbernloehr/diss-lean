import NLS.KdV.HillHminusCommonDirichletSheets
import NLS.KdV.MiuraDirichletSourcePhase

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV.HillHminusPsiChart

/-- The actual phase-rotated Dirac source whose ORDINARY Dirichlet
coordinates are the scalar Hill Dirichlet frequencies. -/
def dirichletSource (P : HillHminusPsiChart) (a : PeriodOneHminusOne) : CoeffPair 2 :=
  sourcePhase (hillMiuraDiagonal (P.miura.lift a))

theorem analyticOnNhd_dirichletSource (P : HillHminusPsiChart) :
    AnalyticOnNhd ℂ P.dirichletSource P.source := by
  intro a ha
  exact (sourcePhase.analyticAt _).comp
    ((hillMiuraDiagonal.analyticAt _).comp (P.miura.lift_analytic a ha.1))

/-- Exact signed label transport, before restricting to real sources
or to high indices. -/
theorem dirichletFrequency_eq_sourcePhase (P : HillHminusPsiChart)
    (n : ℤ) (a : PeriodOneHminusOne) :
    P.dirichletFrequency n a=
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
        (P.dirichletSource a) n := by
  exact congrFun (canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase (by simp) (by norm_num)
    .dirichlet (hillMiuraDiagonal (P.miura.lift a))) n

/-- The moving ORIGINAL scalar energy trace is the actual ordinary
Dirac terminal trace after the source phase. -/
theorem dirichletDiscriminant_eq_sourcePhase (P : HillHminusPsiChart)
    (n : ℕ+) (a : PeriodOneHminusOne) (ha : a∈P.source) :
    sourceBoundaryTerminalDiscriminant (by simp) (by norm_num) .dirichlet (n:ℕ)
      (P.dirichletSource a)=hillHminusDiscriminant a (P.dirichletEnergy n a) := by
  unfold sourceBoundaryTerminalDiscriminant
  rw [← P.dirichletFrequency_eq_sourcePhase]
  change canonicalDiscriminant (by simp)
    (periodOnePotential (sourcePhase (hillMiuraDiagonal (P.miura.lift a))))
      (P.dirichletFrequency (n:ℕ) a)=_
  rw [canonicalDiscriminant_eq_l2_source,l2Discriminant_sourcePhase,
    ← canonicalDiscriminant_eq_l2_source,hillHminusDiscriminant_eq_chart P.miura a ha.1]
  change hillMiuraFrequencyTrace (P.miura.lift a) (P.dirichletFrequency (n:ℕ) a)=
    hillMiuraL2Discriminant (P.miura.lift a)
      ((P.dirichletFrequency (n:ℕ) a)^2-P.miura.energyShift+P.miura.energyShift)
  rw [sub_add_cancel,hillMiuraL2Discriminant_square]

/-- The ORIGINAL physical Hill sheet is exactly the ordinary source
anti-discriminant, with its sign fixed, on every actual common chart. -/
theorem dirichletSheet_eq_sourcePhase (P : HillHminusPsiChart)
    (n : ℕ+) (a : PeriodOneHminusOne) (ha : a∈P.source)
    (hz : P.dirichletFrequency (n:ℕ) a≠0) :
    P.dirichletSheet n a=
      sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet (n:ℕ)
        (P.dirichletSource a) := by
  unfold sourceBoundaryTerminalAntiDiscriminant
  rw [← P.dirichletFrequency_eq_sourcePhase]
  change P.dirichletSheet n a=sourceAntiDiscriminantCandidate (by simp) (by norm_num)
    (sourcePhase (hillMiuraDiagonal (P.miura.lift a))) (P.dirichletFrequency (n:ℕ) a)
  rw [sourceAntiDiscriminant_sourcePhase_miura _ _ hz,dirichletSheet,
    hillHminusDiscriminant_eq_chart P.miura a ha.1]
  change 2*quasiHillL2DirichletTerminal (P.miura.lift a)
      ((P.dirichletFrequency (n:ℕ) a)^2-P.miura.energyShift+P.miura.energyShift)-
    hillMiuraL2Discriminant (P.miura.lift a)
      ((P.dirichletFrequency (n:ℕ) a)^2-P.miura.energyShift+P.miura.energyShift)=_
  rw [sub_add_cancel]

/-- The actual physical derivative-one multiplier is the ORDINARY
source Floquet multiplier. In particular this is equality of values,
not just equality of their characteristic polynomials or squares. -/
theorem dirichletTerminal_eq_sourcePhase (P : HillHminusPsiChart)
    (n : ℕ+) (a : PeriodOneHminusOne) (ha : a∈P.source)
    (hz : P.dirichletFrequency (n:ℕ) a≠0) :
    P.dirichletTerminal n a=
      sourceBoundaryFloquetMultiplier (by simp) (by norm_num) .dirichlet (n:ℕ)
        (P.dirichletSource a) := by
  rw [sourceBoundaryFloquetMultiplier,P.dirichletDiscriminant_eq_sourcePhase n a ha,
    ← P.dirichletSheet_eq_sourcePhase n a ha hz]
  simp only [BoundaryCondition.extensionSign,one_mul,dirichletSheet]
  ring

end NLS.KdV.HillHminusPsiChart
