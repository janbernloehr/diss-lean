import NLS.KdV.HillHminusMiuraActionRatios
import NLS.KdV.HillHminusRetainedMiuraEtaChart
import NLS.KdV.HillHminusUniformActionAmplitude

/-! # Actual finite-head amplitudes at every real rough source

The principal amplitudes of the proved weighted Miura ratios have a
common complex rough ball and two-sided bounds on every finite head.
Physical recovery holds throughout that rough ball, including closed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

theorem exists_hillHminus_principal_amplitude_germ
    (q0 : PeriodOneHminusOne) (V : Set PeriodOneHminusOne) (hV : IsOpen V) (hqV : q0 ∈ V)
    (n : ℕ+) (R : PeriodOneHminusOne → ℂ) (hRa : AnalyticAt ℂ R q0) (hRpos : 0 < (R q0).re)
    (hphysical : ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val ∈ V →
      R (hillOriginalHminusSource p.val) = hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ)) :
    ∃ η a C : ℝ, 0 < η ∧ 0 < a ∧ 0 < C ∧ ball q0 η ⊆ V ∧
      AnalyticOnNhd ℂ (hillHminusActionRatioAmplitude R) (ball q0 η) ∧
      (∀ q ∈ ball q0 η, a ≤ Real.sqrt (1+(n : ℝ))*‖hillHminusActionRatioAmplitude R q‖ ∧
        Real.sqrt (1+(n : ℝ))*‖hillHminusActionRatioAmplitude R q‖ ≤ C) ∧
      ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val ∈ ball q0 η →
        hillHminusActionRatioAmplitude R (hillOriginalHminusSource p.val) =
          hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
  obtain ⟨r,hr,hRr⟩ := hRa.exists_ball_analyticOnNhd
  have hnear := (Complex.continuous_re.continuousAt.comp hRa.continuousAt).tendsto.eventually
    (lt_mem_nhds hRpos)
  obtain ⟨s,hs,hRs⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨t,ht,hVt⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hqV)
  let δ := min r (min s t)
  have hδ : 0 < δ := lt_min hr (lt_min hs ht)
  have hδr : ball q0 δ ⊆ ball q0 r := ball_subset_ball (min_le_left _ _)
  have hδs : ball q0 δ ⊆ ball q0 s :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hδV : ball q0 δ ⊆ V := fun _ h =>
    hVt (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) h)
  have hBa : AnalyticOnNhd ℂ (hillHminusActionRatioAmplitude R) (ball q0 δ) := by
    intro q hq
    have hslit : 2*R q ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      left
      simp only [mul_re,show (2 : ℂ).re=2 from rfl,show (2 : ℂ).im=0 from rfl,
        zero_mul,sub_zero]
      have hp : 0 < (R q).re := hRs (hδs hq)
      linarith
    exact ((Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hslit)).comp
      (f := fun q => 2*R q) (analyticAt_const.mul (hRr q (hδr hq)))).div_const
  have hRn : R q0 ≠ 0 := by intro he; rw [he] at hRpos; exact (lt_irrefl 0) hRpos
  have hBn : 0 < ‖hillHminusActionRatioAmplitude R q0‖ := by
    have he := norm_sq_hillHminusActionRatioAmplitude R q0
    have h := norm_pos_iff.mpr hRn
    nlinarith [norm_nonneg (hillHminusActionRatioAmplitude R q0)]
  have hc := (hBa q0 (mem_ball_self hδ)).continuousAt.norm
  have hnorm := hc.tendsto.eventually (Ioo_mem_nhds (half_lt_self hBn)
    (by linarith : ‖hillHminusActionRatioAmplitude R q0‖ < ‖hillHminusActionRatioAmplitude R q0‖+1))
  obtain ⟨e,he,hBe⟩ := Metric.mem_nhds_iff.mp hnorm
  let η := min δ e
  let w := Real.sqrt (1+(n : ℝ))
  have hw : 0 < w := by dsimp only [w]; positivity
  have hηδ : ball q0 η ⊆ ball q0 δ := ball_subset_ball (min_le_left _ _)
  refine ⟨η,w*(‖hillHminusActionRatioAmplitude R q0‖/2),
    w*(‖hillHminusActionRatioAmplitude R q0‖+1),lt_min hδ he,
    mul_pos hw (half_pos hBn),mul_pos hw (by positivity),
    fun _ h => hδV (hηδ h),hBa.mono hηδ,?_,?_⟩
  · intro q hq
    have hb := hBe (ball_subset_ball (min_le_right δ e) hq)
    exact ⟨mul_le_mul_of_nonneg_left hb.1.le hw.le,mul_le_mul_of_nonneg_left hb.2.le hw.le⟩
  · intro p hp
    have hratio := hphysical p (hδV (hηδ hp))
    have hreal := hillActionGapRatio_real_positive p.val p.property.1 p.property.2 (n : ℕ) n.property
    have hcast : hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ) =
        ((hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ)).re : ℂ) := by
      apply Complex.ext <;> simp only [ofReal_re,ofReal_im,hreal.2]
    rw [hillHminusActionRatioAmplitude,hratio,hcast,← ofReal_ofNat,← ofReal_mul,
      Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hreal.1.le))]
    rfl

theorem exists_hillHminus_arbitrary_base_finite_action_amplitudes
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) (J : Finset ℕ+) :
    ∃ η a C : ℝ, ∃ B : ℕ+ → PeriodOneHminusOne → ℂ, 0 < η ∧ 0 < a ∧ 0 < C ∧
      ∀ n ∈ J, AnalyticOnNhd ℂ (B n) (ball q0 η) ∧
        (∀ q ∈ ball q0 η, a ≤ Real.sqrt (1+(n : ℝ))*‖B n q‖ ∧
          Real.sqrt (1+(n : ℝ))*‖B n q‖ ≤ C) ∧
        ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val ∈ ball q0 η →
          B n (hillOriginalHminusSource p.val) =
            hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
  classical
  obtain ⟨P,c,_hc,hshift,hqP,hreal,houtside,_hlabels,_H,_hstrong⟩ :=
    exists_hillHminus_retained_Miura_eta_chart q0 hr0
  have hreal' : ∀ q ∈ P.miura.domain, IsRealPeriodOneHminusOne q → ∀ k : ℤ,
      P.miura.lift q (-k) = conj (P.miura.lift q k) :=
    fun q hq hr => (periodOneL2Conjugation_fixed_iff _).mp (hreal q hq hr)
  obtain ⟨W,D,V,hV,hqV,_hVP,hR⟩ :=
    P.exists_local_Miura_action_ratios q0 hqP.1 hr0 hreal' houtside c hshift
  let B : ℕ+ → PeriodOneHminusOne → ℂ := fun n => hillHminusActionRatioAmplitude (P.miuraActionRatio D n)
  have hgerm (n : ℕ+) := exists_hillHminus_principal_amplitude_germ q0 V hV hqV n
    (P.miuraActionRatio D n) (hR n).1 (hR n).2.1 (hR n).2.2.2
  have hfinite : ∃ η a C : ℝ, 0 < η ∧ 0 < a ∧ 0 < C ∧ ∀ n ∈ J,
      AnalyticOnNhd ℂ (B n) (ball q0 η) ∧
      (∀ q ∈ ball q0 η, a ≤ Real.sqrt (1+(n : ℝ))*‖B n q‖ ∧
        Real.sqrt (1+(n : ℝ))*‖B n q‖ ≤ C) ∧
      ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val ∈ ball q0 η →
        B n (hillOriginalHminusSource p.val) =
          hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
    induction J using Finset.induction_on with
    | empty => exact ⟨1,1,1,by norm_num,by norm_num,by norm_num,fun n hn => (Finset.notMem_empty n hn).elim⟩
    | @insert n J _ ih =>
      obtain ⟨r,a,C,hr,ha,hC,_hsub,hBa,hbound,hphys⟩ := hgerm n
      obtain ⟨s,b,D,hs,hb,hD,hJ⟩ := ih
      refine ⟨min r s,min a b,C+D,lt_min hr hs,lt_min ha hb,add_pos hC hD,?_⟩
      intro m hm
      rcases Finset.mem_insert.mp hm with hm | hm
      · subst m
        refine ⟨hBa.mono (ball_subset_ball (min_le_left r s)),?_,
          fun p hp => hphys p (ball_subset_ball (min_le_left r s) hp)⟩
        intro q hq
        have h := hbound q (ball_subset_ball (min_le_left r s) hq)
        exact ⟨(min_le_left a b).trans h.1,h.2.trans (by linarith)⟩
      · obtain ⟨hMa,hMb,hMp⟩ := hJ m hm
        refine ⟨hMa.mono (ball_subset_ball (min_le_right r s)),?_,
          fun p hp => hMp p (ball_subset_ball (min_le_right r s) hp)⟩
        intro q hq
        have h := hMb q (ball_subset_ball (min_le_right r s) hq)
        exact ⟨(min_le_right a b).trans h.1,h.2.trans (by linarith)⟩
  obtain ⟨η,a,C,hη,ha,hC,hB⟩ := hfinite
  exact ⟨η,a,C,B,hη,ha,hC,hB⟩

end NLS.KdV
