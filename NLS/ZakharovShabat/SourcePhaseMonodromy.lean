import NLS.ZakharovShabat.L2SourceCharacteristics
import NLS.ZakharovShabat.ClassicalPhaseMonodromy

/-! Exact phase conjugation of the actual physical L2 monodromy on
the original source coefficient space. Density retains every entry and
the actual anti-discriminant sign without a continuous-input hypothesis. -/
noncomputable section
open Set Complex NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

theorem l2Monodromy_sourcePhase_entry (φ : CoeffPair 2) (z : ℂ) (i j : Fin 2) :
    l2Monodromy (sourcePhysicalL2 (sourcePhase φ)) z i j =
      (if i=j then 1 else if i=0 then I else -I)*l2Monodromy (sourcePhysicalL2 φ) z i j := by
  have hc : Continuous (fun ψ : CoeffPair 2 => l2Monodromy (sourcePhysicalL2 ψ) z i j) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    have hm := analyticOnNhd_l2Monodromy_joint (z,sourcePhysicalL2 ψ) (mem_univ _)
    have hij := analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hm i) j
    exact (hij.comp (f := fun η : CoeffPair 2 => (z,sourcePhysicalL2 η))
      (analyticAt_const.prod (sourcePhysicalL2.analyticAt ψ))).continuousAt
  have he := CoeffPair.eq_of_continuous_of_finsupp (p := 2) (by simp)
    (fun ψ => l2Monodromy (sourcePhysicalL2 (sourcePhase ψ)) z i j)
    (fun ψ => (if i=j then (1:ℂ) else if i=0 then I else -I)*l2Monodromy (sourcePhysicalL2 ψ) z i j)
    (hc.comp sourcePhase.continuous) (continuous_const.mul hc) (fun a => by
      have hrot : sourcePhysicalL2 (sourcePhase (CoeffPair.ofFinsupp (p := 2) a)) =
          continuousPotentialL2Class (classicalSourcePhase (finiteSourceCurve a)) :=
        physicalRestrictionL2_of_continuous _ _
          (physicalBase_sourcePhase_compatibility _ _ (finiteSource_physical_compatibility a).1)
      rw [hrot,sourcePhysicalL2_ofFinsupp,l2Monodromy_of_continuous,l2Monodromy_of_continuous]
      fin_cases i <;> fin_cases j
      · simpa using classicalMonodromy_phase_zero_zero (finiteSourceCurve a) z
      · simpa using classicalMonodromy_phase_zero_one (finiteSourceCurve a) z
      · simpa using classicalMonodromy_phase_one_zero (finiteSourceCurve a) z
      · simpa using classicalMonodromy_phase_one_one (finiteSourceCurve a) z)
  exact congrFun he φ

theorem sourceAntiDiscriminant_sourcePhase_eq_monodromy (φ : CoeffPair 2) (z : ℂ) :
    sourceAntiDiscriminantCandidate (by simp) (by norm_num) (sourcePhase φ) z =
      I*(l2Monodromy (sourcePhysicalL2 φ) z 0 1-l2Monodromy (sourcePhysicalL2 φ) z 1 0) := by
  rw [sourceAntiDiscriminantCandidate_eq_l2]
  unfold l2AntiDiscriminant
  rw [l2Monodromy_sourcePhase_entry,l2Monodromy_sourcePhase_entry]
  norm_num
  ring

theorem canonicalDiscriminant_sourcePhase (φ : CoeffPair 2) (z : ℂ) :
    canonicalDiscriminant (by simp) (periodOnePotential (sourcePhase φ)) z =
      canonicalDiscriminant (by simp) (periodOnePotential φ) z := by
  rw [canonicalDiscriminant_eq_l2_source,canonicalDiscriminant_eq_l2_source]
  simp only [l2Discriminant,Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply]
  change l2Monodromy (sourcePhysicalL2 (sourcePhase φ)) z 0 0+
    l2Monodromy (sourcePhysicalL2 (sourcePhase φ)) z 1 1 =
      l2Monodromy (sourcePhysicalL2 φ) z 0 0+l2Monodromy (sourcePhysicalL2 φ) z 1 1
  rw [l2Monodromy_sourcePhase_entry,l2Monodromy_sourcePhase_entry]
  simp

end NLS.ZakharovShabat
