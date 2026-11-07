import NLS.KdV.HillPhysicalDirichletSheetCoefficient
import NLS.KdV.MiuraL2DirichletAuxiliary
import NLS.KdV.HminusOneCharacteristicOrder
import NLS.ZakharovShabat.SourcePhaseMonodromy

/-! The actual Hill terminal sheet is the NEGATIVE anti-discriminant
of the phase-rotated Dirac source. The full physical IVP comparison fixes
the sign at every complex frequency, including zero and collapsed gaps. -/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
open scoped Matrix.Norms.Elementwise
namespace NLS.KdV

theorem quasiHillL2DirichletSheet_eq_rotatedAntiDiscriminant (u : Coeff 2) (z : ℂ) :
    quasiHillL2DirichletSheet u (z^2) =
      -sourceAntiDiscriminantCandidate (by simp) (by norm_num) (sourcePhase (hillMiuraDiagonal u)) z := by
  have hi : miuraStateMap 0 z (1,-I) = (2:ℂ) • ((1,0):ℂ × ℂ) := by
    apply Prod.ext <;> norm_num [miuraStateMap_apply,smul_eq_mul]
  have h := congrArg (fun F : Curve (ℂ × ℂ) =>
    (F ⟨1,by constructor <;> norm_num⟩).1)
      (quasiHillL2SolutionCurve_eq_transformedDirac u z (1,-I))
  rw [hi,quasiHillL2SolutionCurve_smul,l2SolutionCurve_linearCombination] at h
  change 2*(quasiHillL2SolutionCurve u (z^2) (1,0) ⟨1,by constructor <;> norm_num⟩).1 =
    (1*l2Monodromy (sourcePhysicalL2 (hillMiuraDiagonal u)) z 0 0+(-I)*l2Monodromy (sourcePhysicalL2 (hillMiuraDiagonal u)) z 0 1)+
      I*(1*l2Monodromy (sourcePhysicalL2 (hillMiuraDiagonal u)) z 1 0+(-I)*l2Monodromy (sourcePhysicalL2 (hillMiuraDiagonal u)) z 1 1) at h
  have ht := hillMiuraL2Discriminant_eq_quasiHillL2_trace u (z^2)
  rw [hillMiuraL2Discriminant_sq,hillMiuraFrequencyTrace,canonicalDiscriminant_eq_l2_source] at ht
  rw [l2Discriminant,Matrix.trace_fin_two] at ht
  change l2Monodromy (sourcePhysicalL2 (hillMiuraDiagonal u)) z 0 0+
    l2Monodromy (sourcePhysicalL2 (hillMiuraDiagonal u)) z 1 1 =
      (quasiHillL2SolutionCurve u (z^2) (1,0) ⟨1,by constructor <;> norm_num⟩).1+
        quasiHillL2DirichletTerminal u (z^2) at ht
  rw [sourceAntiDiscriminant_sourcePhase_eq_monodromy,quasiHillL2DirichletSheet]
  linear_combination (norm := (ring_nf; simp [I_sq])) h+ht

namespace HillProductEquationPatch

theorem physicalDirichletSheet_eq_rotatedAntiDiscriminant (P : HillProductEquationPatch)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    hillHminusDirichletSheet n q =
      -sourceAntiDiscriminantCandidate (by simp) (by norm_num) (sourcePhase (P.sourcePsi q))
        (P.physicalDirichletFrequency ((n:ℕ):ℤ) q) := by
  let B := P.parent.parent.miuraBall.actionBall
  have hB : q ∈ B.source := (P.parent.subset (P.subset hq)).1
  have he : hillHminusCanonicalDirichlet n q+(B.shift:ℂ) =
      (P.physicalDirichletFrequency ((n:ℕ):ℤ) q)^2 := by
    rw [← P.physicalDirichletFrequency_energy n q hq]
    ring
  rw [hillHminusDirichletSheet_eq_shifted_miura n q (P.source_subset_canonicalDirichlet hq)
    (B.lift q) (B.shift:ℂ) (B.image q hB),he]
  exact quasiHillL2DirichletSheet_eq_rotatedAntiDiscriminant _ _

theorem physicalDirichletFrequency_eq_rotatedDirichlet (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (k : ℤ) :
    P.physicalDirichletFrequency k q =
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet (sourcePhase (P.sourcePsi q)) k := by
  exact congrFun (canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase (by simp) (by norm_num)
    .dirichlet (P.sourcePsi q)) k

end HillProductEquationPatch
end NLS.KdV
