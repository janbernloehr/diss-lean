import NLS.ComplexAnalysis.CosineGapIntegralZero
import NLS.ComplexAnalysis.PrimitiveOnDiscComplement
import NLS.ComplexAnalysis.TwoZeroRootEndpointBound
import NLS.ComplexAnalysis.SegmentPrimitiveBoundary

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem integral_cosineGapPoint_eq_zero_of_zero_period
    (g Q : ℂ → ℂ) (τ δ c : ℂ) (r R : ℝ)
    (hδ : δ ≠ 0) (hr : 0 < r) (hrR : r < R)
    (hgap : segment ℝ (τ-δ) (τ+δ) ⊆ ball c r)
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hQ : AnalyticOnNhd ℂ Q (closedBall c R \ segment ℝ (τ-δ) (τ+δ)))
    (hsq : ∀ z ∈ closedBall c R \ segment ℝ (τ-δ) (τ+δ),
      Q z^2 = (τ-δ-z)*(τ+δ-z))
    (hperiod : (∮ z in C(c,r), g z/Q z) = 0) :
    (∫ θ in (0:ℝ)..Real.pi, g (cosineGapPoint τ δ (θ:ℂ))) = 0 := by
  let K := segment ℝ (τ-δ) (τ+δ)
  let D := closedBall c R \ K
  let Ω := ball c R
  have hclosed : IsClosed K := by
    apply IsCompact.isClosed
    rw [show K = segment ℝ (τ-δ) (τ+δ) from rfl,segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hsub : Ω \ K ⊆ D := fun _ hz => ⟨ball_subset_closedBall hz.1,hz.2⟩
  have hne (z : ℂ) (hz : z ∈ D) : Q z ≠ 0 := by
    have hl : τ-δ-z ≠ 0 := by
      intro he
      exact hz.2 (sub_eq_zero.mp he ▸ left_mem_segment ℝ _ _)
    have hu : τ+δ-z ≠ 0 := by
      intro he
      exact hz.2 (sub_eq_zero.mp he ▸ right_mem_segment ℝ _ _)
    intro he
    exact mul_ne_zero hl hu (by simpa only [he,zero_pow (by norm_num : 2 ≠ 0)] using (hsq z hz).symm)
  have hf : AnalyticOnNhd ℂ (fun z => g z/Q z) D :=
    fun z hz => (hg z hz.1).div (hQ z hz) (hne z hz)
  obtain ⟨F,hF⟩ := exists_primitive_on_disc_complement_of_zero_period
    (fun z => g z/Q z) c (τ-δ) r R hr hrR K hclosed
    (left_mem_segment ℝ _ _) ((convex_segment _ _).starConvex (left_mem_segment ℝ _ _))
    hgap hf hperiod
  have hl : τ-δ ∈ Ω := ball_subset_ball hrR.le (hgap (left_mem_segment ℝ _ _))
  have hab : τ-δ ≠ τ+δ := by
    intro he
    apply hδ
    linear_combination -he/2
  obtain ⟨d,M,ε,hd,hM,hε,hbound⟩ := exists_two_zero_root_endpoint_bound
    g (fun _ => 1) Q D (τ-δ) (τ+δ) hab
    (hg _ (ball_subset_closedBall hl)).continuousAt continuousAt_const one_ne_zero
    (fun z hz => ⟨hne z hz,by rw [hsq z hz]; ring⟩)
  obtain ⟨A,hA⟩ := exists_primitive_segment_left_boundary_limit
    (fun z => g z/Q z) F Ω (τ-δ) (τ+δ) d M ε isOpen_ball hl hab hd hM hε
    (hf.continuousOn.mono hsub) hF (fun z hz hdist => hbound z (hsub hz) hdist)
  exact integral_cosineGapPoint_eq_zero_of_primitive g Q F Ω τ δ A isOpen_ball hδ
    (fun z hz => ball_subset_ball hrR.le (hgap hz))
    (hg.mono ball_subset_closedBall) (hQ.continuousOn.mono hsub)
    (fun z hz => hsq z (hsub hz)) hF hA

end NLS.ComplexAnalysis
