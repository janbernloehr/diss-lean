import NLS.KdV.HillHminusOneUniformGluedActions

/-! # Nonvanishing on the entire open high-action domain

Compactness of the actual gap segment improves pointwise near-one root
normalization to one strict bound on its semicircle mean. Thus every
valid chart has a nonzero ratio, without choosing a uniform-family chart.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem HillHminusActionChartValid.ratio_norm_sub_one_lt_one
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) :
    ‖hillHminusNormalizedActionRatio n r K q-1‖ < 1 := by
  obtain ⟨l,u,hpair⟩ := h.2.2.2.2.2.2
  have hball : segment ℝ l u ⊆
      ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) :=
    (convex_ball _ _).segment_subset hpair.left_mem hpair.right_mem
  have hcompact : IsCompact (segment ℝ l u) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hcont : ContinuousOn (fun z => ‖hillHminusJointNormalizedGapRoot n r K (z,q)-1‖)
      (segment ℝ l u) := ((h.2.2.1.continuousOn.mono hball).sub continuousOn_const).norm
  obtain ⟨z,hz,hmax⟩ := hcompact.exists_isMaxOn ⟨l,left_mem_segment ℝ l u⟩ hcont
  have hmap (a : ℝ) (ha : a ∈ Icc (-1) 1) :
      (l+u)/2+(u-l)/2*(a : ℂ) ∈ segment ℝ l u := by
    have hh : (l+u)/2+(u-l)/2*(a : ℂ) ∈ standardRootGapSegment ((l+u)/2) ((u-l)/2) := ⟨a,ha,rfl⟩
    rw [standardRootGapSegment_eq_segment] at hh
    have hl : (l+u)/2-(u-l)/2 = l := by ring
    have hu : (l+u)/2+(u-l)/2 = u := by ring
    rwa [hl,hu] at hh
  have hc : ContinuousOn (fun a : ℝ => hillHminusJointNormalizedGapRoot n r K
      ((l+u)/2+(u-l)/2*(a : ℂ),q)) (Icc (-1) 1) := by
    intro a ha
    exact ((h.2.2.1 _ (hball (hmap a ha))).continuousAt.comp
      (f := fun a : ℝ => (l+u)/2+(u-l)/2*(a : ℂ)) (by fun_prop)).continuousWithinAt
  rw [hillHminusNormalizedActionRatio_eq_mean n r h.1 K q l u hpair]
  exact (norm_normalizedSemicircleMean_sub_one_le _ _ hc (fun a ha => hmax (hmap a ha))).trans_lt
    (h.2.2.2.2.2.1 z (hball hz))

theorem HillHminusActionChartValid.ratio_ne_zero
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) : hillHminusNormalizedActionRatio n r K q ≠ 0 := by
  intro he
  have hh := h.ratio_norm_sub_one_lt_one
  simp only [he,zero_sub,norm_neg,norm_one,lt_self_iff_false] at hh

theorem hillHminusGluedHighActionRatio_norm_sub_one_lt_one
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusHighActionDomain n) :
    ‖hillHminusGluedHighActionRatio n q-1‖ < 1 := by
  obtain ⟨r,K,V,h,hqV⟩ := hq
  rw [h.glued_ratio_eq hqV]
  exact (h.valid hqV).ratio_norm_sub_one_lt_one

theorem hillHminusGluedHighActionRatio_ne_zero
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusHighActionDomain n) :
    hillHminusGluedHighActionRatio n q ≠ 0 := by
  obtain ⟨r,K,V,h,hqV⟩ := hq
  rw [h.glued_ratio_eq hqV]
  exact (h.valid hqV).ratio_ne_zero

theorem hillHminusGluedHighAction_eq_zero_iff_on_domain
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusHighActionDomain n) :
    hillHminusGluedHighAction n q = 0 ↔ hillHminusGluedHighGapSquare n q = 0 :=
  hillHminusGluedHighAction_eq_zero_iff n q (hillHminusGluedHighActionRatio_ne_zero n q hq)

end NLS.KdV
