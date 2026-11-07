import NLS.KdV.HillCommonZeroSequenceStability
import NLS.ZakharovShabat.SourcePsiQuotientUniformGapProductTail

/-! Transport the actual compact original Hill gap data into the shared
real Dirac gap product. Its uniform midpoint quotient lower bound then
holds for ALL actual complex Hill zero sequences and ALL signed rows
on ONE source ball, including collapsed original gaps. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem frequencySource_real_gapData_mem (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : d ∈ hillHminusEnergyGapData ⟨q,hr⟩) :
    P.frequencySource (d,q) ∈ sourcePeriodicGapRootSet (by norm_num) (by norm_num) (P.sourcePsi q) ×ˢ {P.sourcePsi q} :=
  ⟨fun k => P.parent.energyGapData_independentFrequency_mem_signed_gap q (P.subset hq) hr d hd k,rfl⟩

theorem exists_real_gapData_frequencySource_tube (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (V : Set (Coeff 2 × CoeffPair 2)) (hV : IsOpen V)
    (hbase : sourcePeriodicGapRootSet (by norm_num) (by norm_num) (P.sourcePsi q) ×ˢ {P.sourcePsi q} ⊆ V) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t ∈ cthickening δ (hillHminusEnergyGapData ⟨q,hr⟩ ×ˢ {q}),
        t ∈ P.inputDomain ∧ P.frequencySource t ∈ V := by
  let K := hillHminusEnergyGapData ⟨q,hr⟩ ×ˢ {q}
  let U := P.inputDomain ∩ P.frequencySource ⁻¹' V
  have hK : IsCompact K := (isCompact_hillHminusEnergyGapData ⟨q,hr⟩).prod isCompact_singleton
  have hU : IsOpen U := P.analytic_frequencySource.continuousOn.isOpen_inter_preimage P.inputDomain_open hV
  have hKU : K ⊆ U := by
    rintro ⟨d,y⟩ ⟨hd,hy⟩
    have hyq : y = q := mem_singleton_iff.mp hy
    subst y
    exact ⟨P.real_energyGapData_graph_mem_inputDomain q hq hr d hd,
      hbase (P.frequencySource_real_gapData_mem q hq hr d hd)⟩
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_cthickening_subset_open hU hKU
  exact ⟨δ,hδ,fun t ht => hthick ht⟩

theorem exists_real_gapData_midpoint_quotient_lower_tube (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ t ∈ cthickening δ (hillHminusEnergyGapData ⟨q,hr⟩ ×ˢ {q}),
        t ∈ P.inputDomain ∧ ∀ k : ℤ,
          c ≤ ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
            (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi t.2) k,P.frequencySource t)‖ := by
  let B := P.parent.parent.miuraBall.actionBall
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  let φ : realTypeSourceLocus 2 := ⟨P.sourcePsi q,(hillMiuraRealSource u).property⟩
  obtain ⟨ε,c,hε,hc,hquot⟩ := exists_sourcePsi_midpointQuotient_uniform_lowerBound_near_gapProduct
    (by norm_num) (by norm_num) φ
  let K := sourcePeriodicGapRootSet (by norm_num) (by norm_num) φ.val ×ˢ {φ.val}
  obtain ⟨δ,hδ,htube⟩ := P.exists_real_gapData_frequencySource_tube q hq hr (thickening ε K)
    isOpen_thickening (self_subset_thickening hε K)
  refine ⟨δ,c,hδ,hc,?_⟩
  intro t ht
  have h := htube t ht
  exact ⟨h.1,fun k => hquot (P.frequencySource t) (thickening_subset_cthickening ε K h.2) k⟩

theorem exists_common_zero_sequence_midpoint_quotient_lower_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ball q r ⊆ hillHminusCanonicalZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n : ℕ+, ∀ k : ℤ,
        c ≤ ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
          (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) k,
            P.frequencySource (hillHminusCanonicalZeroSequence n y,y))‖ := by
  obtain ⟨δ,c,hδ,hc,htube⟩ := P.exists_real_gapData_midpoint_quotient_lower_tube q hq hr
  obtain ⟨r,hrpos,hU,hgraph⟩ := exists_common_zero_sequence_gapData_thickening q hr δ hδ
  exact ⟨r,c,hrpos,hc,hU,fun y hy n k => (htube _ (hgraph y hy n)).2 k⟩

end NLS.KdV.HillProductEquationPatch
