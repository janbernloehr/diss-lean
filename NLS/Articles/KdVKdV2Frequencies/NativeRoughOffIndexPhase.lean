import NLS.KdV.HillOriginalOffIndexSourceSeries
import NLS.KdV.HillHminusPairedCorrectionBound
import NLS.SequenceSpaces.PositiveBoundedAnalyticFamily
import NLS.ComplexAnalysis.AnalyticZeroLinearBound

/-! # The actual off-index rough regular phase in its native Banach norm -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by simp
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro j; simp

private theorem offIndexCorrection_zero (n : ℕ+) :
    hillOriginalOffIndexCorrection n (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)=0 := by
  change (∑' j : ℕ, hillOriginalOffIndexCorrectionTerm n
    (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential) j)=0
  rw [show (fun j : ℕ => hillOriginalOffIndexCorrectionTerm n
    (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential) j)=(fun _ => (0 : ℂ)) from ?_,tsum_zero]
  funext j
  unfold hillOriginalOffIndexCorrectionTerm
  split_ifs
  · rfl
  · exact hillRegularAbelianCorrection_closed 0 zero_parity zero_real n n.pos
      (j+1) (by omega) (hillFreeGapHalfLength zero_parity zero_real (j+1) (by omega))

theorem exists_hillHminus_native_offIndex_regular_phase :
    ∃ η C : ℝ, ∃ B : PeriodOneHminusOne → Coeff ⊤,
      0 < η ∧ 0 < C ∧ AnalyticOnNhd ℂ B (ball (0 : PeriodOneHminusOne) η) ∧ B 0=0 ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, ‖B q‖ ≤ C*‖q‖ ∧ ∀ j : ℤ, j ≤ 0 → B q j=0) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
        B (hillPhysicalHminusEmbedding p).val (n : ℤ)=hillOriginalOffIndexCorrection n p := by
  classical
  obtain ⟨P,c,_hc,_hMc,hshift,h0P,hreal,houtside,H⟩ :=
    exists_hillHminusPsiChart_real_form_outside_shift (0 : PeriodOneHminusOne)
      (by intro j; simp) 0
  have h0B := P.mem_sourceBetaDomain_of_real 0 h0P (hreal 0 h0P.1 (by intro j; simp))
  obtain ⟨U,hU,h0U,hUP,A,hA,hbound⟩ :=
    P.exists_local_uniform_sourcePairedBetaCorrection_bound H 0 h0B
  obtain ⟨M,hMa,hMdata⟩ := Coeff.exists_positive_bounded_analytic_lift U hU
    P.sourcePairedBetaCorrection A hA.le
    (fun n => (P.analytic_sourcePairedBetaCorrection H n).mono hUP) hbound
  have hphysical (p : RealPeriodOneHillPotential) (hp : (hillPhysicalHminusEmbedding p).val∈U) (n : ℕ+) :
      M (hillPhysicalHminusEmbedding p).val (n : ℤ)=hillOriginalOffIndexCorrection n p := by
    rw [(hMdata _ hp).2.2]
    have hpP := (hUP hp).1
    exact (P.originalOffIndexCorrection_eq_sourcePaired p hpP hreal (houtside _ hpP.1) c hshift H n).symm
  have hM0 : M 0=0 := by
    apply lp.ext
    funext j
    change M 0 j=0
    by_cases hj : 0 < j
    · let n : ℕ+ := ⟨j.toNat,by omega⟩
      have hn : (n : ℤ)=j := Int.toNat_of_nonneg hj.le
      have hp0 : (hillPhysicalHminusEmbedding (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)).val=0 := by
        change hillOriginalHminusSource (0 : WeightedCoeff SpectralWeight.one.toWeight 2)=0
        exact map_zero _
      have he := hphysical (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential) (hp0 ▸ h0U) n
      rw [hp0,hn,offIndexCorrection_zero] at he
      exact he
    · exact (hMdata 0 h0U).2.1 j (le_of_not_gt hj)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  obtain ⟨s,C,hs,hC,hsMa,hlin⟩ := exists_analytic_zero_linear_bound M (hMa 0 h0U) hM0
  let η := min r s
  have hη : 0 < η := lt_min hr hs
  have hηU : ball (0 : PeriodOneHminusOne) η⊆U := (ball_subset_ball (min_le_left r s)).trans hsub
  refine ⟨η,C,M,hη,hC,hsMa.mono (ball_subset_ball (min_le_right r s)),hM0,?_,?_⟩
  · intro q hq
    exact ⟨hlin q (ball_subset_ball (min_le_right r s) hq),(hMdata q (hηU hq)).2.1⟩
  · intro p hp n
    exact hphysical p (hηU hp) n

end NLS.Articles.KdVKdV2Frequencies
