import NLS.KdV.HillCommonZeroQuotientLowerBound
import NLS.ComplexAnalysis.CompactFamilyNeighborhoodBounds

/-! ONE regular quotient upper bound on ALL original isolating discs
holds before ALL actual complex Hill zero sequences and ALL row indices.
Compact real gap data, the verified all-disc quotient factory, and full
sequence graph stability supply the common complex source neighborhood. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_real_gapData_allDisc_quotient_upper_tube (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ δ Q : ℝ, 0 < δ ∧ 0 ≤ Q ∧
      cthickening δ (hillHminusEnergyGapData ⟨q,hr⟩ ×ˢ {q}) ⊆ P.inputDomain ∧
      ∀ t ∈ cthickening δ (hillHminusEnergyGapData ⟨q,hr⟩ ×ˢ {q}), ∀ k : ℤ, ∀ z ∈ P.discs k,
        ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k (z,P.frequencySource t)‖ ≤ Q := by
  let K := hillHminusEnergyGapData ⟨q,hr⟩ ×ˢ {q}
  let I := {i : ℤ × ℂ // i.2 ∈ P.discs i.1}
  let f : I → (lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) → ℂ := fun i t =>
    sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) i.val.1 (i.val.2,P.frequencySource t)
  have hK : IsCompact K := (isCompact_hillHminusEnergyGapData ⟨q,hr⟩).prod isCompact_singleton
  have hlocal : ∀ x ∈ K, ∃ O, IsOpen O ∧ x ∈ O ∧ O ⊆ P.inputDomain ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ i : I, ∀ t ∈ O, ‖f i t‖ ≤ L := by
    intro x hx
    have hxD : x ∈ P.inputDomain := by
      have hxy : x.2 = q := mem_singleton_iff.mp hx.2
      have hd : x.1 ∈ hillHminusEnergyGapData ⟨q,hr⟩ := hx.1
      simpa only [← hxy] using P.real_energyGapData_graph_mem_inputDomain q hq hr x.1 hd
    obtain ⟨V,hV,hbase,Q,hQ,hquot⟩ := P.quotients.local_allDisk_quotient_bound P.isolating P.V_open
      (P.sourcePsi x.2) (P.image x.2 hxD.2).1 (P.image x.2 hxD.2).2 (P.frequencySource x).1
    let O := P.inputDomain ∩ P.frequencySource ⁻¹' V
    have hO : IsOpen O := P.analytic_frequencySource.continuousOn.isOpen_inter_preimage P.inputDomain_open hV
    exact ⟨O,hO,⟨hxD,hbase⟩,inter_subset_left,Q,hQ,
      fun i t ht => hquot (P.frequencySource t) ht.2 i.val.1 i.val.2 i.property⟩
  obtain ⟨δ,Q,hδ,hQ,hU,hbound⟩ := exists_cthickening_uniform_bound_near_compact K P.inputDomain hK f hlocal
  exact ⟨δ,Q,hδ,hQ,hU,fun t ht k z hz => hbound ⟨(k,z),hz⟩ t ht⟩

theorem exists_common_zero_sequence_allDisc_quotient_upper_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r Q : ℝ, 0 < r ∧ 0 ≤ Q ∧ ball q r ⊆ hillHminusCanonicalZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n : ℕ+, ∀ k : ℤ, ∀ z ∈ P.discs k,
        ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
          (z,P.frequencySource (hillHminusCanonicalZeroSequence n y,y))‖ ≤ Q := by
  obtain ⟨δ,Q,hδ,hQ,_,htube⟩ := P.exists_real_gapData_allDisc_quotient_upper_tube q hq hr
  obtain ⟨r,hrpos,hU,hgraph⟩ := exists_common_zero_sequence_gapData_thickening q hr δ hδ
  exact ⟨r,Q,hrpos,hQ,hU,fun y hy n k z hz => htube _ (hgraph y hy n) k z hz⟩

end NLS.KdV.HillProductEquationPatch
