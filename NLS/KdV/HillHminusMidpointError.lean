import NLS.KdV.HillHminusNativeSourceFactors

/-! The literal midpoint normalization has an inverse-index error from pi.
The denominator is EXACTLY 1+n; its free normalization error is retained. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

theorem sourceNormalizedMidpoint_weighted_error (P : HillHminusPsiChart)
    (a : PeriodOneHminusOne) (n : ℕ+) :
    (1+(n:ℂ))*(P.sourceNormalizedMidpoint n a-(Real.pi:ℂ))=
      sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (P.dirichletSource a) (n:ℤ)-(Real.pi:ℂ) := by
  rw [sourceNormalizedMidpoint,sourcePeriodicMidpointDisplacement_apply]
  have hd : (1+(n:ℂ))≠0 := by exact_mod_cast (show (1+(n:ℝ))≠0 by positivity)
  simp only [Int.cast_natCast]
  rw [mul_sub,mul_div_cancel₀ _ hd]
  ring

theorem exists_local_native_sourceNormalizedMidpoint_error (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.sourceBetaDomain ∧
      ∃ C : ℝ, ∃ M : PeriodOneHminusOne → Coeff ⊤, 0<C ∧ AnalyticOnNhd ℂ M U ∧
        ∀ a∈U, ‖M a‖≤C ∧ (∀ j : ℤ, j≤0 → M a j=0) ∧
          ∀ n : ℕ+, M a (n:ℤ)=(1+(n:ℂ))*(P.sourceNormalizedMidpoint n a-(Real.pi:ℂ)) := by
  obtain ⟨_N,_hN,V,hV,hqV,R,hR,hbound⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement (p := 2) (by norm_num) (by norm_num)
      (P.dirichletSource q) (by norm_num : (0:ℝ)<1)
  let U := P.sourceBetaDomain∩P.dirichletSource ⁻¹' V
  have hc : ContinuousOn P.dirichletSource P.sourceBetaDomain :=
    P.analyticOnNhd_dirichletSource.continuousOn.mono inter_subset_left
  have hU : IsOpen U := hc.isOpen_inter_preimage P.sourceBetaDomain_open hV
  let f : ℕ+ → PeriodOneHminusOne → ℂ := fun n a =>
    (1+(n:ℂ))*(P.sourceNormalizedMidpoint n a-(Real.pi:ℂ))
  have ha (n : ℕ+) : AnalyticOnNhd ℂ (f n) U := by
    intro a ha
    exact analyticAt_const.mul (((((H.original_theta_common_domain.symmetric_analytic _ ha.1.2 (n:ℕ)).1).comp
      (f := P.dirichletSource) (P.analyticOnNhd_dirichletSource a ha.1.1)).div_const).sub analyticAt_const)
  have hb (a : PeriodOneHminusOne) (ha : a∈U) (n : ℕ+) : ‖f n a‖≤R+Real.pi := by
    have hd := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0)
      (sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (P.dirichletSource a)) (n:ℤ)).trans
        (hbound _ ha.2).1
    change ‖(1+(n:ℂ))*(P.sourceNormalizedMidpoint n a-(Real.pi:ℂ))‖≤_
    rw [P.sourceNormalizedMidpoint_weighted_error]
    exact (norm_sub_le _ _).trans (by
      rw [Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
      exact add_le_add hd le_rfl)
  obtain ⟨M,hMa,hM⟩ := Coeff.exists_positive_bounded_analytic_lift U hU f (R+Real.pi) (by positivity) ha hb
  exact ⟨U,hU,⟨hq,hqV⟩,inter_subset_left,R+Real.pi,M,by positivity,hMa,hM⟩

end NLS.KdV.HillHminusPsiChart
