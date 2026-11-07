import NLS.KdV.HillProductEquationLocalBounds
import NLS.KdV.HillRealEnergyGapDataPlacement
import NLS.ComplexAnalysis.CompactFamilyNeighborhoodBounds

/-! The FULL compact original real gap-data slice lies in the common
placed-input domain. ONE closed thickening and ONE full equation norm
bound work around that entire slice BEFORE ALL numerator indices. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem real_energyGapData_graph_mem_inputDomain (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : d ∈ hillHminusEnergyGapData ⟨q,hr⟩) : (d,q) ∈ P.inputDomain := by
  refine ⟨⟨P.parent.energyGapData_mem_frequencyDomain q (P.subset hq) hr d hd,?_⟩,hq⟩
  intro k
  exact P.isolating.gap (P.sourcePsi q) (P.image q hq).2 k
    (P.parent.energyGapData_independentFrequency_mem_signed_gap q (P.subset hq) hr d hd k)

theorem exists_real_gapData_uniform_equation_thickening (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 ≤ L ∧
      cthickening δ (hillHminusEnergyGapData ⟨q,hr⟩ ×ˢ {q}) ⊆ P.inputDomain ∧
      ∀ n : ℕ+, ∀ t ∈ cthickening δ (hillHminusEnergyGapData ⟨q,hr⟩ ×ˢ {q}), ‖P.equation n t‖ ≤ L := by
  apply exists_cthickening_uniform_bound_near_compact _ P.inputDomain
    ((isCompact_hillHminusEnergyGapData ⟨q,hr⟩).prod isCompact_singleton) P.equation
  rintro ⟨d,y⟩ ⟨hd,hy⟩
  have hyq : y = q := mem_singleton_iff.mp hy
  subst y
  exact P.exists_local_uniform_equation_bound (d,q) (P.real_energyGapData_graph_mem_inputDomain q hq hr d hd)

theorem exists_actual_real_uniform_equation_balls (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ R L : ℝ, 0 < R ∧ 0 ≤ L ∧ ∀ d ∈ hillHminusEnergyGapData ⟨q,hr⟩,
      closedBall (d,q) R ⊆ P.inputDomain ∧
        ∀ n : ℕ+, ∀ t ∈ closedBall (d,q) R, ‖P.equation n t‖ ≤ L := by
  obtain ⟨R,L,hR,hL,hdom,hbound⟩ := P.exists_real_gapData_uniform_equation_thickening q hq hr
  refine ⟨R,L,hR,hL,?_⟩
  intro d hd
  have hball : closedBall (d,q) R ⊆ cthickening R (hillHminusEnergyGapData ⟨q,hr⟩ ×ˢ {q}) := by
    intro t ht
    exact mem_cthickening_of_dist_le t (d,q) R _ ⟨hd,mem_singleton q⟩ ht
  exact ⟨hball.trans hdom,fun n t ht => hbound n t (hball ht)⟩

end NLS.KdV.HillProductEquationPatch
