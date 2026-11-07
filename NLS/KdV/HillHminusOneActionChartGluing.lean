import NLS.KdV.HillHminusOneActionChart

/-! # Uniqueness of actual high Hill actions across square and radius charts

The common actual branch root fixes the filled square on the overlap.
Principal-root normalization then fixes the intrinsic root, including
at cut points by continuity. The resulting action ratio is independent
of both the filled square and the isolating radius.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillHminusActionChartValid.root_eq_on_overlap
    {q : PeriodOneHminusOne} {n : ℕ+} {r s : ℝ} {K L : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (k : HillHminusActionChartValid n s L q) :
    EqOn (fun z => hillHminusJointNormalizedGapRoot n r K (z,q))
      (fun z => hillHminusJointNormalizedGapRoot n s L (z,q))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ∩
        ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*s)) := by
  obtain ⟨l,u,hpair⟩ := h.2.2.2.2.2.2
  obtain ⟨a,b,kpair⟩ := k.2.2.2.2.2.2
  apply continuous_eqOn_of_dense_on_open (segment ℝ l u)ᶜ _
    (dense_complex_segment_complement l u) (isOpen_ball.inter isOpen_ball)
    _ _ (h.2.2.1.continuousOn.mono inter_subset_left) (k.2.2.1.continuousOn.mono inter_subset_right)
  intro z hz
  have hP : hillHminusGapPolynomial n r (z,q) ≠ 0 := by
    rw [hpair.gapPolynomial_eq h.1 z]
    apply mul_ne_zero
    · intro he
      exact hz.2 (sub_eq_zero.mp he ▸ left_mem_segment ℝ l u)
    · intro he
      exact hz.2 (sub_eq_zero.mp he ▸ right_mem_segment ℝ l u)
  have hden : (4*((Real.pi : ℂ)*(n : ℕ))^2) ≠ 0 := by simp [Real.pi_ne_zero,n.ne_zero]
  have he := (h.2.2.2.2.1 z hz.1.1).symm.trans
    ((h.square_eq_on_overlap k hz.1).trans (k.2.2.2.2.1 z hz.1.2))
  rw [← hpair.gapPolynomial_eq_other_radius kpair h.1 k.1 z] at he
  have hs : hillHminusJointNormalizedGapRoot n r K (z,q)^2 =
      hillHminusJointNormalizedGapRoot n s L (z,q)^2 :=
    mul_left_cancel₀ (neg_ne_zero.mpr hP) ((div_left_inj' hden).mp he)
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with heq | heq
  · exact heq
  · have hp := re_pos_of_norm_sub_one_lt_one _ (h.2.2.2.2.2.1 z hz.1.1)
    have hq := re_pos_of_norm_sub_one_lt_one _ (k.2.2.2.2.2.1 z hz.1.2)
    have hh := congrArg Complex.re heq
    simp only [neg_re] at hh
    linarith

theorem HillHminusActionChartValid.symmetric_data_eq
    {q : PeriodOneHminusOne} {n : ℕ+} {r s : ℝ} {K L : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (k : HillHminusActionChartValid n s L q) :
    hillHminusGapMidpoint n r q = hillHminusGapMidpoint n s q ∧
      hillHminusSquaredHalfGap n r q = hillHminusSquaredHalfGap n s q := by
  obtain ⟨l,u,hpair⟩ := h.2.2.2.2.2.2
  obtain ⟨a,b,kpair⟩ := k.2.2.2.2.2.2
  have hd := (hpair.align_other_radius kpair).symmetric_gap_data k.1
  exact ⟨(hpair.symmetric_gap_data h.1).1.trans hd.1.symm,
    (hpair.symmetric_gap_data h.1).2.trans hd.2.symm⟩

theorem HillHminusActionChartValid.ratio_eq
    {q : PeriodOneHminusOne} {n : ℕ+} {r s : ℝ} {K L : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (k : HillHminusActionChartValid n s L q) :
    hillHminusNormalizedActionRatio n r K q = hillHminusNormalizedActionRatio n s L q := by
  obtain ⟨l,u,hpair⟩ := h.2.2.2.2.2.2
  obtain ⟨a,b,kpair⟩ := k.2.2.2.2.2.2
  have kpair' := hpair.align_other_radius kpair
  rw [hillHminusNormalizedActionRatio_eq_mean n r h.1 K q l u hpair,
    hillHminusNormalizedActionRatio_eq_mean n s k.1 L q l u kpair']
  unfold normalizedSemicircleMean
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  exact congrArg (fun w : ℂ => (Real.sin θ : ℂ)^2*w) (h.root_eq_on_overlap k
    ⟨hpair.affine_gap_mem_ball _ ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩,
      kpair'.affine_gap_mem_ball _ ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩⟩)

theorem HillHminusActionChartValid.action_eq_ratio
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u))
    (hw : Γ.windingIntegral ((l+u)/2) = 1) :
    hillHminusHighContourAction n r K q l u Γ =
      (u-l)^2/(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusNormalizedActionRatio n r K q :=
  hillHminusHighContourAction_eq_gap_square_mul_ratio n r h.1 K q l u hpair h.2.2.1
    h.2.2.2.2.1 h.2.2.2.1 Γ hΓ hw

theorem HillHminusActionChartValid.action_eq_other_chart
    {q : PeriodOneHminusOne} {n : ℕ+} {r s : ℝ} {K L : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (k : HillHminusActionChartValid n s L q)
    (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u) (kpair : HillHminusHighGapPair q n s l u)
    (Γ Γ₀ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u))
    (hΓ₀ : Γ₀.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*s) \ segment ℝ l u))
    (hw : Γ.windingIntegral ((l+u)/2) = 1) (hw₀ : Γ₀.windingIntegral ((l+u)/2) = 1) :
    hillHminusHighContourAction n r K q l u Γ = hillHminusHighContourAction n s L q l u Γ₀ := by
  rw [h.action_eq_ratio l u hpair Γ hΓ hw,k.action_eq_ratio l u kpair Γ₀ hΓ₀ hw₀,h.ratio_eq k]

end NLS.KdV
