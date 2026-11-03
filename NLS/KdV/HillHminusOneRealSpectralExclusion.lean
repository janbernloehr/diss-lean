import NLS.KdV.HillHminusOneEnergyRootChartAgreement
import NLS.KdV.HillHminusOneRealMiuraCharts
import NLS.KdV.HillHminusOneSourcePrimitive
import NLS.SequenceSpaces.PeriodOneRealScaling

/-! # Nonreal energy exclusion for the actual real Hminus1 trace

Constructed real Miura charts supply a nonzero canonical square root at
all nonreal energies. This excludes nonreal periodic spectral zeros for
every physically real rough potential and places these energies in the
original free-normalized source continuation domain.
-/
noncomputable section
open Set Complex
namespace NLS.KdV

theorem hillHminusRadicand_ne_zero_of_real_of_im_ne_zero
    (q : PeriodOneHminusOne) (hq : periodOneHminusConjugation q = q)
    (energy : ℂ) (hi : energy.im ≠ 0) : hillHminusRadicand q energy ≠ 0 := by
  obtain ⟨C,hqC,_,hc,hr⟩ := exists_real_hillHminusMiuraChart q hq
  have hd := C.nonreal_mem_energyRootDomain q hc (hr q hqC hq).2 energy hi
  have hs := C.energyRoot_sq q hqC energy hd
  change C.energyRoot q energy ^ 2 = hillHminusRadicand q energy at hs
  rw [← hs]
  exact pow_ne_zero _ (C.energyRoot_ne_zero q energy hd)

theorem nonreal_mem_hillHminusContinuationDomain
    (q : PeriodOneHminusOne) (hq : periodOneHminusConjugation q = q)
    (energy : ℂ) (hi : energy.im ≠ 0) :
    (energy,q) ∈ hillHminusContinuationDomain := by
  rw [mem_hillHminusContinuationDomain_iff]
  refine ⟨Or.inr hi,?_⟩
  intro r _
  exact hillHminusRadicand_ne_zero_of_real_of_im_ne_zero _
    (periodOneHminusConjugation_real_smul_fixed r q hq) energy hi

end NLS.KdV
