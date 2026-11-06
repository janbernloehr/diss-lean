import NLS.KdV.HillHminusPairedCorrectionBound
import NLS.ZakharovShabat.SourceGapWeightedEtaOriginalSequence
import NLS.SequenceSpaces.PositiveBoundedAnalyticFamily

/-! # Native rough source factors for the full Abelian coordinates

The own-index eta is retained inside its gap-weighted analytic sequence.
The midpoint normalization and the full beta correction with its central
slot removed are bounded analytic symbols on a common neighborhood before
all positive indices. No open-gap restriction enters these constructions.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

def sourceEtaSequence (P : HillHminusPsiChart) (q : PeriodOneHminusOne) : Coeff 2 :=
  sourceGapWeightedEtaSequence (by norm_num) (by norm_num) P.family.roots 1 (P.dirichletSource q)

theorem analytic_sourceEtaSequence (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots) :
    AnalyticOnNhd ℂ P.sourceEtaSequence P.sourceBetaDomain := by
  intro q hq
  exact (H.gapWeighted_original_sequence_analytic 1 (by simp) _ hq.2).comp
    (f := P.dirichletSource) (P.analyticOnNhd_dirichletSource q hq.1)

theorem sourceEtaSequence_apply (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain) (j : ℤ) :
    P.sourceEtaSequence q j=sourceGapWeightedEtaCoordinate (by norm_num) (by norm_num)
      j P.family.roots 1 (P.dirichletSource q) :=
  H.gapWeighted_original_sequence_apply _ hq.2 1 (by simp) j

def sourceNoncentralBeta (P : HillHminusPsiChart) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  P.sourceBetaCorrection (n : ℕ) q-
    sourceAngularBeta (by norm_num) (by norm_num) ((n : ℕ) : ℤ) 0
      P.family.roots (P.dirichletSource q)

theorem analytic_sourceNoncentralBeta (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.sourceNoncentralBeta n) P.sourceBetaDomain := by
  have hn : (0 : ℤ)≠(n : ℕ) := by have := n.pos; omega
  intro q hq
  exact (P.analytic_sourceBetaCorrection H (n : ℕ) q hq).sub
    ((H.beta_original_analytic ((n : ℕ) : ℤ) 0 hn _ hq.2).comp
      (f := P.dirichletSource) (P.analyticOnNhd_dirichletSource q hq.1))

theorem exists_local_uniform_sourceNoncentralBeta_bound (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.sourceBetaDomain ∧
      ∃ B : ℝ, 0 < B ∧ ∀ a∈U, ∀ n : ℕ+, ‖P.sourceNoncentralBeta n a‖ ≤ B := by
  obtain ⟨V,hV,hqV,_hVW,B,hB,hbound⟩ :=
    H.exists_local_uniform_absolute_beta_bound (P.dirichletSource q) hq.2
  let U := P.sourceBetaDomain ∩ P.dirichletSource ⁻¹' V
  have hc : ContinuousOn P.dirichletSource P.sourceBetaDomain :=
    P.analyticOnNhd_dirichletSource.continuousOn.mono inter_subset_left
  refine ⟨U,hc.isOpen_inter_preimage P.sourceBetaDomain_open hV,⟨hq,hqV⟩,
    inter_subset_left,2*B,by positivity,?_⟩
  intro a ha n
  have hs := hbound _ ha.2 ((n : ℕ) : ℤ)
  have hcentral := (hs.1.le_tsum 0 (fun _ _ => norm_nonneg _)).trans hs.2
  have hn : (0 : ℤ)≠(n : ℕ) := by have := n.pos; omega
  simp only [sourceAngularBetaSeriesTerm,if_neg hn] at hcentral
  have hfull : ‖P.sourceBetaCorrection (n : ℕ) a‖ ≤ B :=
    (norm_tsum_le_tsum_norm hs.1).trans hs.2
  exact (norm_sub_le _ _).trans (by linarith)

/-- The full noncentral beta exponential is one native bounded symbol. -/
theorem exists_local_native_sourceNoncentralBeta_exp (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.sourceBetaDomain ∧
      ∃ C : ℝ, ∃ M : PeriodOneHminusOne → Coeff ⊤, 0 < C ∧ AnalyticOnNhd ℂ M U ∧
        ∀ a∈U, ‖M a‖ ≤ C ∧ (∀ j : ℤ, j ≤ 0 → M a j=0) ∧
          ∀ n : ℕ+, M a (n : ℤ)=Complex.exp (I*P.sourceNoncentralBeta n a) := by
  obtain ⟨U,hU,hqU,hUP,B,hB,hbound⟩ := P.exists_local_uniform_sourceNoncentralBeta_bound H q hq
  have ha (n : ℕ+) : AnalyticOnNhd ℂ
      (fun a => Complex.exp (I*P.sourceNoncentralBeta n a)) U := by
    intro a ha
    exact (analyticAt_const.mul (P.analytic_sourceNoncentralBeta H n a (hUP ha))).cexp'
  have hb (a : PeriodOneHminusOne) (ha : a∈U) (n : ℕ+) :
      ‖Complex.exp (I*P.sourceNoncentralBeta n a)‖ ≤ Real.exp B := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    exact (Complex.re_le_norm _).trans (by simpa only [norm_mul,Complex.norm_I,one_mul] using hbound a ha n)
  obtain ⟨M,hMa,hM⟩ := Coeff.exists_positive_bounded_analytic_lift U hU
    (fun n a => Complex.exp (I*P.sourceNoncentralBeta n a)) (Real.exp B)
    (Real.exp_pos B).le ha hb
  exact ⟨U,hU,hqU,hUP,Real.exp B,M,Real.exp_pos B,hMa,hM⟩

def sourceNormalizedMidpoint (P : HillHminusPsiChart) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  canonicalPeriodicMidpoint (by norm_num) (by norm_num)
    (periodOnePotential (P.dirichletSource q)) (periodOnePotential_mem _) (n : ℕ)/
      (1+(n : ℕ) : ℂ)

/-- The frequency midpoint divided by 1+n is one bounded analytic symbol. -/
theorem exists_local_native_sourceNormalizedMidpoint (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.sourceBetaDomain ∧
      ∃ C : ℝ, ∃ M : PeriodOneHminusOne → Coeff ⊤, 0 < C ∧ AnalyticOnNhd ℂ M U ∧
        ∀ a∈U, ‖M a‖ ≤ C ∧ (∀ j : ℤ, j ≤ 0 → M a j=0) ∧
          ∀ n : ℕ+, M a (n : ℤ)=P.sourceNormalizedMidpoint n a := by
  obtain ⟨_N,_hN,V,hV,hqV,R,hR,hbound⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement (p := 2) (by norm_num) (by norm_num)
      (P.dirichletSource q) (show (0 : ℝ)<1 by norm_num)
  let U := P.sourceBetaDomain ∩ P.dirichletSource ⁻¹' V
  have hc : ContinuousOn P.dirichletSource P.sourceBetaDomain :=
    P.analyticOnNhd_dirichletSource.continuousOn.mono inter_subset_left
  have hU : IsOpen U := hc.isOpen_inter_preimage P.sourceBetaDomain_open hV
  have ha (n : ℕ+) : AnalyticOnNhd ℂ (P.sourceNormalizedMidpoint n) U := by
    intro a ha
    exact (((H.original_theta_common_domain.symmetric_analytic _ ha.1.2 (n : ℕ)).1).comp
      (f := P.dirichletSource) (P.analyticOnNhd_dirichletSource a ha.1.1)).div_const
  have hb (a : PeriodOneHminusOne) (ha : a∈U) (n : ℕ+) :
      ‖P.sourceNormalizedMidpoint n a‖ ≤ Real.pi+R := by
    let m := canonicalPeriodicMidpoint (p := 2) (by norm_num) (by norm_num)
      (periodOnePotential (P.dirichletSource a)) (periodOnePotential_mem _) (n : ℕ)
    have hd : ‖m-(Real.pi : ℂ)*(n : ℕ)‖ ≤ R := by
      have hh := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0)
        (sourcePeriodicMidpointDisplacement (p := 2) (by norm_num) (by norm_num)
          (P.dirichletSource a)) ((n : ℕ) : ℤ)).trans (hbound _ ha.2).1
      change ‖sourcePeriodicMidpointDisplacement (p := 2) (by norm_num) (by norm_num)
        (P.dirichletSource a) ((n : ℕ) : ℤ)‖≤R at hh
      rw [sourcePeriodicMidpointDisplacement_apply] at hh
      simpa only [m,Int.cast_natCast] using hh
    have hm : ‖m‖ ≤ Real.pi*(n : ℝ)+R := by
      have hh := norm_add_le ((Real.pi : ℂ)*(n : ℕ)) (m-(Real.pi : ℂ)*(n : ℕ))
      rw [add_sub_cancel, norm_mul, norm_real, Real.norm_of_nonneg Real.pi_pos.le,
        Complex.norm_natCast] at hh
      exact hh.trans (add_le_add_right hd _)
    have hn : (0 : ℝ)≤(n : ℝ) := by positivity
    have hden : ‖(1+(n : ℕ) : ℂ)‖=1+(n : ℝ) := by
      rw [← Nat.cast_one,← Nat.cast_add,Complex.norm_natCast,Nat.cast_add,Nat.cast_one]
    change ‖m/(1+(n : ℕ) : ℂ)‖≤_
    rw [norm_div,hden,div_le_iff₀ (by positivity : (0 : ℝ)<1+(n : ℝ))]
    nlinarith [Real.pi_pos]
  obtain ⟨M,hMa,hM⟩ := Coeff.exists_positive_bounded_analytic_lift U hU
    P.sourceNormalizedMidpoint (Real.pi+R) (by positivity) ha hb
  exact ⟨U,hU,⟨hq,hqV⟩,inter_subset_left,Real.pi+R,M,by positivity,hMa,hM⟩

end NLS.KdV.HillHminusPsiChart
