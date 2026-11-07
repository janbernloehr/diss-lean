import NLS.KdV.HillRetainedPeriodSequences
import NLS.KdV.HminusOneIndependentHillFrequencies
import NLS.ZakharovShabat.SourcePsiOriginalOmega

/-! A COMMON open independent-energy input domain before ALL Hill
numerator indices. Actual real indexed zero data belong to it whenever
the actual source gaps lie in the original isolating discs. This is a
domain for the independent inputs, not yet an analytic actual zero map. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

def hillProductPlacementDomain (D : ℤ → Set ℂ) : Set (ℂ × lp (fun _ : ℕ+ => ℂ) 2) :=
  LpSequence.quadraticFrequencyDomain Real.pi ∩
    hillIndependentFrequencyDisplacement ⁻¹' sourcePsiOriginalRootPlacement D

theorem isOpen_hillProductPlacementDomain
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C) :
    IsOpen (hillProductPlacementDomain D) :=
  analyticOnNhd_hillIndependentFrequencyDisplacement.continuousOn.isOpen_inter_preimage
    (LpSequence.isOpen_quadraticFrequencyDomain Real.pi Real.pi_pos) hD.isOpen_originalRootPlacement

theorem HillHminusPsiBall.actual_zero_data_mem_productPlacementDomain (B : HillHminusPsiBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q)
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (hψV : hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q) ∈ V) :
    ((B.parent.miuraBall.actionBall.shift:ℂ),hillHminusPsiZeroDisplacement n ⟨q,hr⟩) ∈
      hillProductPlacementDomain D :=
  ⟨B.actual_zero_data_mem_frequencyDomain n q hq hr,
    fun k => hD.gap _ hψV k (B.actual_independentFrequency_mem_signed_gap n q hq hr k)⟩

end NLS.KdV
