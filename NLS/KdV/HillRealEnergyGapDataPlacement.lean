import NLS.KdV.HillRealEnergyGapDataCompact
import NLS.KdV.HminusOneIndependentHillFrequencies

/-! EVERY full original real energy-gap selection belongs to the common
analytic frequency domain and maps into every original signed gap. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillHminusPsiBall

theorem energyGapData_mem_frequencyDomain (B : HillHminusPsiBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : d ∈ hillHminusEnergyGapData ⟨q,hr⟩) :
    ((B.parent.miuraBall.actionBall.shift:ℂ),d) ∈ LpSequence.quadraticFrequencyDomain Real.pi := by
  let u : PeriodOneRealL2 := ⟨B.parent.miuraBall.actionBall.lift q,
    B.parent.miuraBall.actionBall.lift_real q (B.subset hq).1 hr⟩
  intro m
  obtain ⟨E,hE,he⟩ := hd m
  have h := (hillMiura_frequency_of_original_gap q hr u B.parent.miuraBall.actionBall.shift
    (B.parent.miuraBall.actionBall.image q (B.subset hq).1)
    (B.parent.miuraBall.actionBall.outside q (B.subset hq).1) m E hE).1
  change hillEnergySequenceZero m d+(B.parent.miuraBall.actionBall.shift:ℂ) ∈ slitPlane
  rw [← he]
  exact h

theorem energyGapData_independentFrequency_mem_signed_gap (B : HillHminusPsiBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : d ∈ hillHminusEnergyGapData ⟨q,hr⟩) (k : ℤ) :
    hillIndependentFrequency ((B.parent.miuraBall.actionBall.shift:ℂ),d) k ∈
      sourcePeriodicSegment (by norm_num) (by norm_num)
        (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) k := by
  let u : PeriodOneRealL2 := ⟨B.parent.miuraBall.actionBall.lift q,
    B.parent.miuraBall.actionBall.lift_real q (B.subset hq).1 hr⟩
  obtain ⟨σ,hσ,he⟩ := exists_real_hill_energy_gap_selection ⟨q,hr⟩ d hd
  rw [hillIndependentFrequency_eq_real_balanced σ B.parent.miuraBall.actionBall.shift d he]
  exact hillBalancedGapFrequency_mem_segment q hr u B.parent.miuraBall.actionBall.shift
    (B.parent.miuraBall.actionBall.image q (B.subset hq).1)
    (B.parent.miuraBall.actionBall.outside q (B.subset hq).1) σ hσ k

end NLS.KdV.HillHminusPsiBall
