import NLS.KdV.HillAbelianRealEnergyGap

/-! Original-energy uniqueness compares DIFFERENT Miura patches and
shifts. A common convex tube contains the entire ORIGINAL real gap,
including collapsed gaps; the ACTUAL physical divisor value agrees. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_common_original_energy_gap_neighborhood (P T : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hqP : q ∈ P.source) (hqT : q ∈ T.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ Convex ℝ Ω ∧
      segment ℝ (hillHminusLabels q hr (2*(m:ℕ)-1):ℂ) (hillHminusLabels q hr (2*(m:ℕ)):ℂ) ⊆ Ω ∧
      ∀ E ∈ Ω, (E,q) ∈ P.abelianFilledEnergyDomain m ∧ (E,q) ∈ T.abelianFilledEnergyDomain m := by
  let S := segment ℝ (hillHminusLabels q hr (2*(m:ℕ)-1):ℂ) (hillHminusLabels q hr (2*(m:ℕ)):ℂ)
  let U := {E : ℂ | (E,q) ∈ P.abelianFilledEnergyDomain m ∧ (E,q) ∈ T.abelianFilledEnergyDomain m}
  have hU : IsOpen U := ((P.abelianFilledEnergyDomain_open m).preimage (continuous_id.prodMk continuous_const)).inter
    ((T.abelianFilledEnergyDomain_open m).preimage (continuous_id.prodMk continuous_const))
  have hSU : S ⊆ U := fun E hE =>
    ⟨P.original_energy_segment_mem_filled_domain m q hqP hr hE,T.original_energy_segment_mem_filled_domain m q hqT hr hE⟩
  have hcompact : IsCompact S := by
    rw [show S = segment ℝ (hillHminusLabels q hr (2*(m:ℕ)-1):ℂ) (hillHminusLabels q hr (2*(m:ℕ)):ℂ) from rfl,segment_eq_image_lineMap]
    exact isCompact_Icc.image (by
      change Continuous (fun t : ℝ => AffineMap.lineMap (hillHminusLabels q hr (2*(m:ℕ)-1):ℂ) (hillHminusLabels q hr (2*(m:ℕ)):ℂ) t)
      simp_rw [AffineMap.lineMap_apply_module']
      fun_prop)
  obtain ⟨δ,hδ,hsub⟩ := hcompact.exists_thickening_subset_open hU hSU
  exact ⟨thickening δ S,isOpen_thickening,(convex_segment _ _).thickening δ,
    self_subset_thickening hδ S,hsub⟩

theorem offIndexAbelianEnergyQuotient_eq_on_original_gap_neighborhood
    (P T : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hqP : q ∈ P.source) (hqT : q ∈ T.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ Convex ℝ Ω ∧
      segment ℝ (hillHminusLabels q hr (2*(m:ℕ)-1):ℂ) (hillHminusLabels q hr (2*(m:ℕ)):ℂ) ⊆ Ω ∧
      (∀ E ∈ Ω, (E,q) ∈ P.abelianFilledEnergyDomain m ∧ (E,q) ∈ T.abelianFilledEnergyDomain m) ∧
      EqOn (fun E => P.offIndexAbelianEnergyQuotient n m (E,q))
        (fun E => T.offIndexAbelianEnergyQuotient n m (E,q)) Ω := by
  obtain ⟨Ω,hΩ,hconv,hseg,hdom⟩ := P.exists_common_original_energy_gap_neighborhood T m q hqP hqT hr
  let a : ℂ := hillHminusLabels q hr (2*(m:ℕ)-1)
  have ha : a ∈ Ω := hseg (left_mem_segment ℝ _ _)
  have hDa : hillHminusRadicand q a = 0 := (hillHminusLabels_roots_iff q hr a).mpr ⟨_,rfl⟩
  have hfinite : ∀ E ∈ Ω, analyticOrderAt (hillHminusRadicand q) E ≠ ⊤ := by
    obtain ⟨N,V,_,_,hqV,hcontrol⟩ := exists_hillHminus_central_controls q
    have hc := hcontrol N le_rfl q hqV
    exact fun E _ => analyticOrderAt_ne_top_on_connected isPreconnected_univ
      (analyticOnNhd_hillHminusRadicand q) (mem_univ _) (hc.separator_ne_zero (hillCentralSeparator N:ℂ) rfl) (mem_univ E)
  have hP : AnalyticOnNhd ℂ (fun E => P.offIndexAbelianEnergyQuotient n m (E,q)) Ω := by
    intro E hE
    exact (P.analytic_offIndexAbelianEnergyQuotient n m hmn (E,q) (hdom E hE).1).comp
      (f := fun e : ℂ => (e,q)) (analyticAt_id.prod analyticAt_const)
  have hT : AnalyticOnNhd ℂ (fun E => T.offIndexAbelianEnergyQuotient n m (E,q)) Ω := by
    intro E hE
    exact (T.analytic_offIndexAbelianEnergyQuotient n m hmn (E,q) (hdom E hE).2).comp
      (f := fun e : ℂ => (e,q)) (analyticAt_id.prod analyticAt_const)
  refine ⟨Ω,hΩ,hconv,hseg,hdom,?_⟩
  exact radicand_equation_solution_unique (hillHminusRadicand q) (fun E => hillHminusCanonicalPsi n (E,q))
    _ _ Ω a hΩ hconv.isPreconnected ha hDa ((analyticOnNhd_hillHminusRadicand q).mono (subset_univ _)) hfinite hP hT
    (fun E hE => P.offIndexAbelianEnergyQuotient_equation n m hmn q E (hdom E hE).1)
    (fun E hE => T.offIndexAbelianEnergyQuotient_equation n m hmn q E (hdom E hE).2)

theorem physicalOffIndexAbelianValue_eq_actual_sheet_mul_energy_quotient_of_real
    (P : HillProductEquationPatch) (n m : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    P.physicalOffIndexAbelianValue n m q = hillHminusDirichletSheet m q*
      P.offIndexAbelianEnergyQuotient n m (hillHminusCanonicalDirichlet m q,q) := by
  let z := P.physicalDirichletFrequency ((m:ℕ):ℤ) q
  have hzD := P.physicalDirichletFrequency_mem_disc q (P.real_mem_physicalDirichletSource q hq hr) ((m:ℕ):ℤ)
  have hz : 0 < z.re := P.abelianGapDisc_re_pos_of_real m q hq hr z hzD
  rw [← P.physicalDirichletFrequency_energy m q hq,P.offIndexAbelianEnergyQuotient_at_positive_frequency n m q z hz]
  unfold physicalOffIndexAbelianValue physicalDirichletRootCoefficient
  ring

theorem physicalOffIndexAbelianValue_eq_of_real_overlap (P T : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne)
    (hqP : q ∈ P.source) (hqT : q ∈ T.source) (hr : IsRealPeriodOneHminusOne q) :
    P.physicalOffIndexAbelianValue n m q = T.physicalOffIndexAbelianValue n m q := by
  obtain ⟨Ω,_,_,hseg,_,heq⟩ := P.offIndexAbelianEnergyQuotient_eq_on_original_gap_neighborhood T n m hmn q hqP hqT hr
  have hμ : hillHminusCanonicalDirichlet m q ∈ Ω := by
    rw [hillHminusCanonicalDirichlet_eq_real q hr m]
    exact hseg (ofReal_mem_convex_of_mem_Icc _ (convex_segment _ _) _ _ _
      (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _) (hillHminusDirichletLabels_mem_gap q hr m))
  rw [P.physicalOffIndexAbelianValue_eq_actual_sheet_mul_energy_quotient_of_real n m q hqP hr,
    T.physicalOffIndexAbelianValue_eq_actual_sheet_mul_energy_quotient_of_real n m q hqT hr]
  exact congrArg (fun v => hillHminusDirichletSheet m q*v) (heq hμ)

end NLS.KdV.HillProductEquationPatch
