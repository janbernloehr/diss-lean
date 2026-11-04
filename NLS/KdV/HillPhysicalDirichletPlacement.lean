import NLS.KdV.HillAbelianRegularRootSheets
import NLS.KdV.HminusOneCanonicalDirichletAsymptotics
import NLS.ZakharovShabat.AuxiliaryGapSegmentPlacement

/-! ONE OPEN complex native domain places the ACTUAL auxiliary
Dirichlet frequencies in ALL original assigned discs BEFORE ALL
signed indices. It contains EVERY real point of the original patch. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def physicalDirichletFrequency (P : HillProductEquationPatch) (m : ℤ) (q : PeriodOneHminusOne) : ℂ :=
  hillMiuraDiracDirichlet (P.parent.parent.miuraBall.actionBall.lift q) m

def physicalDirichletSource (P : HillProductEquationPatch) : Set PeriodOneHminusOne :=
  P.source ∩ (fun q => hillMiuraDirichletDisplacement (P.parent.parent.miuraBall.actionBall.lift q)) ⁻¹'
    sourcePsiOriginalRootPlacement P.discs

theorem analytic_physicalDirichletFrequency (P : HillProductEquationPatch) (m : ℤ) :
    AnalyticOnNhd ℂ (P.physicalDirichletFrequency m) P.source :=
  (P.parent.parent.auxiliary_analytic m).mono (fun _ hq => (P.parent.subset (P.subset hq)).1)

theorem physicalDirichlet_displacement_restores_frequency (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (m : ℤ) :
    displacedRoots (hillMiuraDirichletDisplacement (P.parent.parent.miuraBall.actionBall.lift q)) m =
      P.physicalDirichletFrequency m q := by
  rw [displacedRoots,hillMiuraDirichletDisplacement_apply]
  change (Real.pi:ℂ)*m+(P.physicalDirichletFrequency m q-(Real.pi:ℂ)*m) = P.physicalDirichletFrequency m q
  ring

theorem physicalDirichletSource_open (P : HillProductEquationPatch) : IsOpen P.physicalDirichletSource := by
  have hA : AnalyticOnNhd ℂ (fun q => hillMiuraDirichletDisplacement (P.parent.parent.miuraBall.actionBall.lift q)) P.source :=
    P.parent.parent.analytic_auxiliaryDisplacement.mono (fun _ hq => (P.parent.subset (P.subset hq)).1)
  exact hA.continuousOn.isOpen_inter_preimage P.source_open P.isolating.isOpen_originalRootPlacement

theorem physicalDirichletFrequency_mem_disc (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) (m : ℤ) :
    P.physicalDirichletFrequency m q ∈ ball (P.centers m:ℂ) (P.radii m) := by
  have h := hq.2 m
  rw [P.physicalDirichlet_displacement_restores_frequency q m,P.discs_eq m] at h
  exact h

theorem real_mem_physicalDirichletSource (P : HillProductEquationPatch) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) : q ∈ P.physicalDirichletSource := by
  refine ⟨hq,?_⟩
  intro m
  rw [P.physicalDirichlet_displacement_restores_frequency q m]
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  exact P.isolating.gap (P.sourcePsi q) (P.image q hq).2 m
    (canonicalAuxiliaryPeriodOneRoots_mem_sourcePeriodicSegment_of_realType (by norm_num) (by norm_num)
      .dirichlet (P.sourcePsi q) (hillMiuraRealSource u).property m)

theorem physicalDirichletFrequency_energy (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    P.physicalDirichletFrequency ((m:ℕ):ℤ) q^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ) = hillHminusCanonicalDirichlet m q := by
  rw [P.parent.parent.canonical_dirichlet_eq m q (P.parent.subset (P.subset hq)).1]
  rfl

end NLS.KdV.HillProductEquationPatch
