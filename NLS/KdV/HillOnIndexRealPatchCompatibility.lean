import NLS.KdV.HillOnIndexSimpleEndpoint
import NLS.KdV.HillOnIndexRealClosedGap
import NLS.KdV.HillAbelianRealPatchCompatibility

/-! Diagonal Cartesian factors from ANY different Miura patches and
shifts agree at EVERY REAL common source. Open gaps use the SAME
intrinsic native-energy branch system and ORIGINAL endpoint value;
closed gaps use actual real auxiliary interlacing and zero factors. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem onIndexEnergy_coefficients_eq_on_real_open_gap_neighborhood (P T : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hqP : q ∈ P.source) (hqT : q ∈ T.source) (hr : IsRealPeriodOneHminusOne q)
    (hgap : hillHminusCanonicalGapSquare n q ≠ 0) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ Convex ℝ Ω ∧
      segment ℝ (hillHminusLabels q hr (2*(n:ℕ)-1):ℂ) (hillHminusLabels q hr (2*(n:ℕ)):ℂ) ⊆ Ω ∧
      (∀ E ∈ Ω, (E,q) ∈ P.abelianFilledEnergyDomain n ∧ (E,q) ∈ T.abelianFilledEnergyDomain n) ∧
      ∀ E ∈ Ω, P.onIndexEnergyEven n (E,q) = T.onIndexEnergyEven n (E,q) ∧
        P.onIndexEnergyOdd n (E,q) = T.onIndexEnergyOdd n (E,q) := by
  obtain ⟨Ω,hΩ,hconv,hseg,hdom⟩ := P.exists_common_original_energy_gap_neighborhood T n q hqP hqT hr
  let a : ℂ := hillHminusLabels q hr (2*(n:ℕ)-1)
  have ha : a ∈ Ω := hseg (left_mem_segment ℝ _ _)
  have hDa : hillHminusRadicand q a = 0 := (hillHminusLabels_roots_iff q hr a).mpr ⟨_,rfl⟩
  have hDprime := P.native_radicand_deriv_at_real_open_gap_left_ne_zero n q hqP hr hgap
  have hPA : AnalyticOnNhd ℂ (fun E => P.onIndexEnergyEven n (E,q)) Ω := by
    intro E hE
    exact (P.analytic_onIndexEnergyEven n (E,q) (hdom E hE).1).comp
      (f := fun e : ℂ => (e,q)) (analyticAt_id.prod analyticAt_const)
  have hPB : AnalyticOnNhd ℂ (fun E => P.onIndexEnergyOdd n (E,q)) Ω := by
    intro E hE
    exact (P.analytic_onIndexEnergyOdd n (E,q) (hdom E hE).1).comp
      (f := fun e : ℂ => (e,q)) (analyticAt_id.prod analyticAt_const)
  have hTA : AnalyticOnNhd ℂ (fun E => T.onIndexEnergyEven n (E,q)) Ω := by
    intro E hE
    exact (T.analytic_onIndexEnergyEven n (E,q) (hdom E hE).2).comp
      (f := fun e : ℂ => (e,q)) (analyticAt_id.prod analyticAt_const)
  have hTB : AnalyticOnNhd ℂ (fun E => T.onIndexEnergyOdd n (E,q)) Ω := by
    intro E hE
    exact (T.analytic_onIndexEnergyOdd n (E,q) (hdom E hE).2).comp
      (f := fun e : ℂ => (e,q)) (analyticAt_id.prod analyticAt_const)
  have hbase : P.onIndexEnergyEven n (a,q) = T.onIndexEnergyEven n (a,q) :=
    (P.onIndexEnergyEven_at_original_left_endpoint n q hqP hr).trans (T.onIndexEnergyEven_at_original_left_endpoint n q hqT hr).symm
  refine ⟨Ω,hΩ,hconv,hseg,hdom,?_⟩
  exact analytic_branch_system_unique (hillHminusRadicand q) (fun E => I*hillHminusCanonicalPsi n (E,q))
    _ _ _ _ Ω a hΩ hconv.isPreconnected ha ((analyticOnNhd_hillHminusRadicand q).mono (subset_univ _)) hDa hDprime
    hPA hPB hTA hTB hbase
    (fun E hE => (P.onIndexEnergy_branch_system n q E (hdom E hE).1).1)
    (fun E hE => (P.onIndexEnergy_branch_system n q E (hdom E hE).1).2)
    (fun E hE => (T.onIndexEnergy_branch_system n q E (hdom E hE).2).1)
    (fun E hE => (T.onIndexEnergy_branch_system n q E (hdom E hE).2).2)

theorem physicalOnIndexCartesian_eq_of_real_overlap (P T : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hqP : q ∈ P.source) (hqT : q ∈ T.source) (hr : IsRealPeriodOneHminusOne q) :
    P.physicalOnIndexCartesianPlus n q = T.physicalOnIndexCartesianPlus n q ∧
      P.physicalOnIndexCartesianMinus n q = T.physicalOnIndexCartesianMinus n q := by
  by_cases hgap : hillHminusCanonicalGapSquare n q = 0
  · have hp := P.physicalOnIndexCartesian_zero_of_real_closed_gap n q hqP hr hgap
    have hT := T.physicalOnIndexCartesian_zero_of_real_closed_gap n q hqT hr hgap
    exact ⟨hp.1.trans hT.1.symm,hp.2.trans hT.2.symm⟩
  · obtain ⟨Ω,_,_,hseg,_,heq⟩ := P.onIndexEnergy_coefficients_eq_on_real_open_gap_neighborhood T n q hqP hqT hr hgap
    have hμ : hillHminusCanonicalDirichlet n q ∈ Ω := by
      rw [hillHminusCanonicalDirichlet_eq_real q hr n]
      exact hseg (ofReal_mem_convex_of_mem_Icc _ (convex_segment _ _) _ _ _
        (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _) (hillHminusDirichletLabels_mem_gap q hr n))
    have hAB := heq _ hμ
    have hp := P.physicalOnIndexCartesian_eq_original_energy_coefficients_of_real n q hqP hr
    have hT := T.physicalOnIndexCartesian_eq_original_energy_coefficients_of_real n q hqT hr
    rw [hAB.1,hAB.2] at hp
    exact ⟨hp.1.trans hT.1.symm,hp.2.trans hT.2.symm⟩

end NLS.KdV.HillProductEquationPatch
