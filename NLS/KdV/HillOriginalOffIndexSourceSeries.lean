import NLS.KdV.HillOriginalPairedBeta
import NLS.KdV.HillHminusPairedSourceCorrection

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat NLS.SequenceSpaces
open scoped ComplexConjugate
namespace NLS.KdV

/-- The literal ORIGINAL scalar correction series with its selected
own-index term removed, and no central scalar term introduced. -/
def hillOriginalOffIndexCorrectionTerm (n : ℕ+) (q : RealPeriodOneHillPotential) (j : ℕ) : ℂ :=
  if j+1=(n:ℕ) then 0 else
    hillRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos (j+1) (by omega)

def hillOriginalOffIndexCorrection (n : ℕ+) (q : RealPeriodOneHillPotential) : ℂ :=
  ∑' j : ℕ, hillOriginalOffIndexCorrectionTerm n q j

namespace HillHminusPsiChart
variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
  (hq : hillOriginalHminusSource q.val∈P.source)
  (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
    P.miura.lift a (-k)=conj (P.miura.lift a k))
  (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
  (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)
  (H : SourceLemma12_12Data (by norm_num) (by norm_num)
    P.family.originalDomain P.family.domain P.family.roots)
include hq hreal houtside hshift H

/-- Exact termwise identification, including every low, endpoint and
collapsed slot and the deleted selected slot. -/
theorem sourcePairedBetaTerm_eq_original (n : ℕ+) (j : ℕ) :
    P.sourcePairedBetaTerm n (hillOriginalHminusSource q.val) j=hillOriginalOffIndexCorrectionTerm n q j := by
  by_cases hj : j+1=(n:ℕ)
  · have hz : (j:ℤ)+1=(n:ℕ) := by exact_mod_cast hj
    simp only [sourcePairedBetaTerm,pairedPositiveOffIndexTerm,hillOriginalOffIndexCorrectionTerm,if_pos hj,if_pos hz]
  · have hz : (j:ℤ)+1≠(n:ℕ) := by exact_mod_cast hj
    have hn := n.pos
    have hneg : -((j:ℤ)+1)≠(n:ℕ) := by omega
    simp only [sourcePairedBetaTerm,pairedPositiveOffIndexTerm,hillOriginalOffIndexCorrectionTerm,
      if_neg hj,if_neg hz,sourceAngularBetaSeriesTerm,if_neg hneg]
    exact (P.originalCorrection_eq_paired_source_beta q hq hreal houtside c hshift H n
      (⟨j+1,by omega⟩ : ℕ+) (fun h => hj (congrArg Subtype.val h))).symm

theorem originalOffIndexCorrection_summable_norm (n : ℕ+) :
    Summable (fun j : ℕ => ‖hillOriginalOffIndexCorrectionTerm n q j‖) := by
  have ha := P.mem_sourceBetaDomain_of_real (hillOriginalHminusSource q.val) hq
    (hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2))
  exact (P.summable_norm_sourcePairedBetaTerm H n _ ha).congr
    (fun j => congrArg norm (P.sourcePairedBetaTerm_eq_original q hq hreal houtside c hshift H n j))

/-- The literal ORIGINAL scalar off-index sum is the already checked
complex-analytic paired source correction, with the exact normalization. -/
theorem originalOffIndexCorrection_eq_sourcePaired (n : ℕ+) :
    hillOriginalOffIndexCorrection n q=P.sourcePairedBetaCorrection n (hillOriginalHminusSource q.val) := by
  unfold hillOriginalOffIndexCorrection sourcePairedBetaCorrection
  exact tsum_congr (fun j => (P.sourcePairedBetaTerm_eq_original q hq hreal houtside c hshift H n j).symm)

end HillHminusPsiChart

/-- Every original real source has ONE complex H-minus-one neighborhood
BEFORE ALL positive indices. On it, the actual original off-index scalar
correction has the actual paired-source analytic extension and locally
uniformly convergent series, including endpoint and collapsed potentials. -/
theorem exists_hillOriginal_offIndexCorrection_common_complex_extension
    (q : RealPeriodOneHillPotential) (M : ℝ) :
    ∃ P : HillHminusPsiChart, ∃ c : ℝ, ∃ U : Set PeriodOneHminusOne,
      0<c ∧ M<c ∧ P.miura.energyShift=(c:ℂ)^2 ∧ IsOpen U ∧
      hillOriginalHminusSource q.val∈U ∧ U⊆P.sourceBetaDomain ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (P.sourcePairedBetaCorrection n) U ∧
        TendstoUniformlyOn (P.sourcePairedBetaPartialSum n) (P.sourcePairedBetaCorrection n) atTop U) ∧
      ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val∈U → ∀ n : ℕ+,
        hillOriginalOffIndexCorrection n p=P.sourcePairedBetaCorrection n (hillOriginalHminusSource p.val) ∧
        Summable (fun j : ℕ => ‖hillOriginalOffIndexCorrectionTerm n p j‖) ∧
        ∀ j : ℕ, P.sourcePairedBetaTerm n (hillOriginalHminusSource p.val) j=
          hillOriginalOffIndexCorrectionTerm n p j := by
  obtain ⟨P,c,hc,hMc,hshift,hqP,hreal,houtside,H⟩ :=
    exists_hillHminusPsiChart_real_form_outside_shift (hillOriginalHminusSource q.val)
      (hillOriginalHminusSource_real q.val q.property.2) M
  have hqB := P.mem_sourceBetaDomain_of_real (hillOriginalHminusSource q.val) hqP
    (hreal _ hqP.1 (hillOriginalHminusSource_real q.val q.property.2))
  obtain ⟨U,hU,hqU,hUB,hconv⟩ := P.exists_local_uniform_sourcePairedBetaCorrection H _ hqB
  refine ⟨P,c,U,hc,hMc,hshift,hU,hqU,hUB,?_,?_⟩
  · intro n
    exact ⟨(P.analytic_sourcePairedBetaCorrection H n).mono hUB,hconv n⟩
  · intro p hp n
    have hpP := (hUB hp).1
    exact ⟨P.originalOffIndexCorrection_eq_sourcePaired p hpP hreal (houtside _ hpP.1) c hshift H n,
      P.originalOffIndexCorrection_summable_norm p hpP hreal (houtside _ hpP.1) c hshift H n,
      P.sourcePairedBetaTerm_eq_original p hpP hreal (houtside _ hpP.1) c hshift H n⟩

end NLS.KdV
