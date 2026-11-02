import NLS.KdV.ClassicalHillGapScaleBounds
import NLS.ComplexAnalysis.AnalyticCutContour
import NLS.ComplexAnalysis.TwoZeroCriticalLocalization

/-! # Weighted cut-period bounds on gap-length circles

The analytic cut may include a critical pole inside the gap circle.
This keeps the diagonal squared denominator in the contour deformation.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem circleIntegral_cut_eq_gap_circle (f : ℂ → ℂ) (c l u : ℂ) (R : ℝ)
    (hR : 0 < R) (hl : l ∈ closedBall c (R/8)) (hu : u ∈ closedBall c (R/8))
    (hgap : 0 < ‖l-u‖) (K : Set ℂ) (hK : K ⊆ ball ((l+u)/2) ‖l-u‖)
    (hf : AnalyticOnNhd ℂ f (ball c R \ K)) :
    (∮ z in C(c,R/2), f z) = ∮ z in C((l+u)/2,‖l-u‖), f z := by
  have hl' := mem_closedBall_iff_norm.mp hl
  have hu' := mem_closedBall_iff_norm.mp hu
  have hmid := norm_complex_midpoint_sub_le l u c (R/8) hl' hu'
  have hg : ‖l-u‖ ≤ R/4 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub l c u
    rw [norm_sub_rev c u] at ht
    linarith
  have hinner : closedBall ((l+u)/2) ‖l-u‖ ⊆ ball c (R/2) := by
    intro z hz
    have hz' := mem_closedBall_iff_norm.mp hz
    have ht := norm_sub_le_norm_sub_add_norm_sub z ((l+u)/2) c
    apply mem_ball_iff_norm.mpr
    linarith
  exact (circleIntegral_eq_of_analytic_cut_nestedCircles f (ball c R) K hf
    ((l+u)/2) c ‖l-u‖ (R/2) hgap (by positivity) hK
    (fun _ hz => hinner (ball_subset_closedBall (hK hz)))
    (fun _ hz => ball_subset_closedBall (hinner hz))
    (closedBall_subset_ball (by linarith))).symm

theorem straight_gap_mem_gap_ball (l u : ℂ) (hgap : 0 < ‖l-u‖) :
    segment ℝ l u ⊆ ball ((l+u)/2) ‖l-u‖ := by
  apply (convex_ball _ _).segment_subset
  · apply mem_ball_iff_norm.mpr
    rw [show l-(l+u)/2 = (l-u)/2 by ring,norm_div,norm_ofNat]
    linarith
  · apply mem_ball_iff_norm.mpr
    rw [show u-(l+u)/2 = -(l-u)/2 by ring,norm_div,norm_neg,norm_ofNat]
    linarith

theorem norm_power_resolvent_cut_le (B : ℂ → ℂ) (c l u d : ℂ)
    (R A t b : ℝ) (m : ℕ) (hR : 0 < R) (hA : 0 ≤ A) (ht : 0 < t) (hb : 0 < b)
    (hl : l ∈ closedBall c (R/8)) (hu : u ∈ closedBall c (R/8))
    (hB : AnalyticOnNhd ℂ B (ball c R \ segment ℝ l u))
    (hcollapsed : l = u → AnalyticOnNhd ℂ B (ball c R))
    (hd : d ∉ ball c R)
    (hbound : ∀ z ∈ closedBall ((l+u)/2) ‖l-u‖ \ segment ℝ l u, ‖B z‖ ≤ A*‖l-u‖/t)
    (hsep : ∀ z ∈ sphere ((l+u)/2) ‖l-u‖, b ≤ ‖z-d‖) :
    ‖∮ z in C(c,R/2), B z^m/(z-d)^2‖ ≤
      2*Real.pi*A^m*‖l-u‖^(m+1)/(t^m*b^2) := by
  have houter : closedBall c (R/2) ⊆ ball c R := closedBall_subset_ball (by linarith)
  have hne (z : ℂ) (hz : z ∈ ball c R) : z-d ≠ 0 := by
    intro he
    exact hd (sub_eq_zero.mp he ▸ hz)
  by_cases he : l = u
  · have hf : AnalyticOnNhd ℂ (fun z => B z^m/(z-d)^2) (closedBall c (R/2)) := by
      intro z hz
      exact (((hcollapsed he) z (houter hz)).pow m).div
        ((analyticAt_id.sub analyticAt_const).pow 2) (pow_ne_zero _ (hne z (houter hz)))
    have hz := circleIntegral_eq_zero_of_differentiable_on_off_countable (by positivity) countable_empty
      hf.continuousOn (fun z hz => (hf z (ball_subset_closedBall hz.1)).differentiableAt)
    rw [hz,norm_zero,he,sub_self,norm_zero,zero_pow (by omega : m+1 ≠ 0),mul_zero,zero_div]
  have hg : 0 < ‖l-u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hseg := straight_gap_mem_gap_ball l u hg
  have hf : AnalyticOnNhd ℂ (fun z => B z^m/(z-d)^2) (ball c R \ segment ℝ l u) := by
    intro z hz
    exact ((hB z hz).pow m).div ((analyticAt_id.sub analyticAt_const).pow 2) (pow_ne_zero _ (hne z hz.1))
  rw [circleIntegral_cut_eq_gap_circle _ c l u R hR hl hu hg _ hseg hf]
  have hi : ‖∮ z in C((l+u)/2,‖l-u‖), B z^m/(z-d)^2‖ ≤
      2*Real.pi*‖l-u‖*((A*‖l-u‖/t)^m/b^2) := by
    apply circleIntegral.norm_integral_le_of_norm_le_const hg.le
    intro z hz
    have hnseg : z ∉ segment ℝ l u := by
      intro hzin
      have hh := mem_ball_iff_norm.mp (hseg hzin)
      rw [mem_sphere_iff_norm.mp hz] at hh
      exact (lt_irrefl _ hh)
    rw [norm_div,norm_pow,norm_pow]
    gcongr
    · exact hbound z ⟨sphere_subset_closedBall hz,hnseg⟩
    · exact hsep z hz
  apply hi.trans_eq
  rw [div_pow,mul_pow,pow_succ]
  ring

theorem norm_power_critical_cut_le (B : ℂ → ℂ) (c l u d : ℂ)
    (R A t : ℝ) (m : ℕ) (hR : 0 < R) (hA : 0 ≤ A) (ht : 0 < t)
    (hl : l ∈ closedBall c (R/8)) (hu : u ∈ closedBall c (R/8))
    (hgap : 0 < ‖l-u‖) (hcritical : ‖d-(l+u)/2‖ ≤ ‖l-u‖/4)
    (hB : AnalyticOnNhd ℂ B (ball c R \ segment ℝ l u))
    (hbound : ∀ z ∈ closedBall ((l+u)/2) ‖l-u‖ \ segment ℝ l u, ‖B z‖ ≤ A*‖l-u‖/t) :
    ‖∮ z in C(c,R/2), B z^(m+2)/(z-d)^2‖ ≤
      8*Real.pi*A^(m+2)*‖l-u‖^(m+1)/t^(m+2) := by
  let K : Set ℂ := segment ℝ l u ∪ {d}
  have hseg := straight_gap_mem_gap_ball l u hgap
  have hK : K ⊆ ball ((l+u)/2) ‖l-u‖ := by
    intro z hz
    rcases hz with hz | hz
    · exact hseg hz
    · obtain rfl := mem_singleton_iff.mp hz
      exact mem_ball_iff_norm.mpr (hcritical.trans_lt (by linarith))
  have hf : AnalyticOnNhd ℂ (fun z => B z^(m+2)/(z-d)^2) (ball c R \ K) := by
    intro z hz
    have hne : z-d ≠ 0 := by
      intro he
      exact hz.2 (Or.inr (mem_singleton_iff.mpr (sub_eq_zero.mp he)))
    exact ((hB z ⟨hz.1,fun h => hz.2 (Or.inl h)⟩).pow (m+2)).div
      ((analyticAt_id.sub analyticAt_const).pow 2) (pow_ne_zero _ hne)
  rw [circleIntegral_cut_eq_gap_circle _ c l u R hR hl hu hgap K hK hf]
  have hi : ‖∮ z in C((l+u)/2,‖l-u‖), B z^(m+2)/(z-d)^2‖ ≤
      2*Real.pi*‖l-u‖*((A*‖l-u‖/t)^(m+2)/(‖l-u‖/2)^2) := by
    apply circleIntegral.norm_integral_le_of_norm_le_const hgap.le
    intro z hz
    have hnseg : z ∉ segment ℝ l u := by
      intro hzin
      have hh := mem_ball_iff_norm.mp (hseg hzin)
      rw [mem_sphere_iff_norm.mp hz] at hh
      exact (lt_irrefl _ hh)
    rw [norm_div,norm_pow,norm_pow]
    gcongr
    · exact hbound z ⟨sphere_subset_closedBall hz,hnseg⟩
    · exact gap_circle_critical_separation l u d z hcritical hz
  apply hi.trans_eq
  simp only [div_pow,mul_pow,pow_add,pow_two,pow_one]
  field_simp
  ring

end NLS.KdV
