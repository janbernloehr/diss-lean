import NLS.ComplexAnalysis.UpperLogarithmBoundary

/-! # Continuous upper closure and compact bounds from full boundary limits -/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.ComplexAnalysis

def realBoundaryExtension (F : ℂ → ℂ) (B : ℝ → ℂ) (z : ℂ) : ℂ :=
  if z.im = 0 then B z.re else F z

theorem continuousOn_realBoundaryExtension_upper (F : ℂ → ℂ) (B : ℝ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → ContinuousAt F z)
    (hlim : ∀ x : ℝ, Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (B x))) :
    ContinuousOn (realBoundaryExtension F B) {z : ℂ | 0 ≤ z.im} := by
  have hB := continuous_real_boundary_of_upper_limits F B hlim
  intro z hz
  by_cases hz0 : z.im = 0
  · have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz0]
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hlim z.re) ε hε
    obtain ⟨η, hη, hbr⟩ := Metric.continuousAt_iff.mp (hB.continuousAt (x := z.re)) ε hε
    refine ⟨min δ η, lt_min hδ hη, fun w hw hdist => ?_⟩
    have hdistδ : dist w (z.re : ℂ) < δ := by rw [← hzC]; exact hdist.trans_le (min_le_left _ _)
    have hdistη : dist w.re z.re < η := by
      have he : dist w.re z.re ≤ dist w z := by
        simpa only [dist_eq_norm, Real.norm_eq_abs, ← sub_re] using abs_re_le_norm (w - z)
      exact he.trans_lt (hdist.trans_le (min_le_right _ _))
    dsimp only [realBoundaryExtension]
    rw [if_pos hz0]
    split_ifs with hw0
    · exact hbr hdistη
    · exact hb (lt_of_le_of_ne hw (Ne.symm hw0)) hdistδ
  · apply ((hF z (lt_of_le_of_ne hz (Ne.symm hz0))).congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [(isOpen_ne_fun continuous_im continuous_const).mem_nhds hz0] with w hw
    exact if_neg hw

theorem exists_bound_realBoundaryExtension_on_closedBall (F : ℂ → ℂ) (B : ℝ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → ContinuousAt F z)
    (hlim : ∀ x : ℝ, Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (B x)))
    (hreflect : ∀ z : ℂ, z.im ≠ 0 → F (conj z) = -conj (F z)) (c r : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ closedBall (c : ℂ) r, ‖realBoundaryExtension F B z‖ ≤ M := by
  let K := closedBall (c : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_im)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_realBoundaryExtension_upper F B hF hlim).mono (fun _ hz => hz.2))
  refine ⟨max M 0, le_max_right _ _, fun z hz => ?_⟩
  by_cases hi : 0 ≤ z.im
  · exact (hM z ⟨hz, hi⟩).trans (le_max_left _ _)
  · have hneg : z.im < 0 := not_le.mp hi
    have hc : conj z ∈ K := by
      constructor
      · simpa only [mem_closedBall, dist_conj_comm, conj_ofReal] using hz
      · change 0 ≤ (conj z).im
        simpa only [conj_im, neg_nonneg] using hneg.le
    have he : ‖realBoundaryExtension F B (conj z)‖ = ‖realBoundaryExtension F B z‖ := by
      simp only [realBoundaryExtension, conj_im, neg_eq_zero,
        if_neg hneg.ne, hreflect z hneg.ne, norm_neg, norm_conj]
    exact (he ▸ hM (conj z) hc).trans (le_max_left _ _)

end NLS.ComplexAnalysis
