import NLS.ComplexAnalysis.PrimitiveRadialContinuation

/-!
# Extending an annular primitive across a star-convex cut complement

An outer annular primitive extends to the whole disc minus an enclosed
closed cut that is star-convex at a point of the cut. The center of
radial continuation can differ from the enclosing circles' center.
Thus a moving complex gap can use its midpoint and retain its assigned
fixed isolating circles.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem exists_primitive_on_disc_complement_of_annular_primitive
    (f G : ℂ → ℂ) (d c : ℂ) (r R : ℝ) (hr : 0 ≤ r) (hrR : r < R)
    (K : Set ℂ) (hKclosed : IsClosed K) (hc : c ∈ K) (hKstar : StarConvex ℝ c K)
    (hKinner : K ⊆ ball d r) (hf : AnalyticOnNhd ℂ f (ball d R \ K))
    (hG : ∀ z ∈ ball d R \ closedBall d r, HasDerivAt G (f z) z) :
    ∃ F : ℂ → ℂ, EqOn F G (ball d R \ closedBall d r) ∧
      ∀ z ∈ ball d R \ K, HasDerivAt F (f z) z := by
  let Ω := ball d R \ K
  let A := ball d R \ closedBall d r
  have hAΩ : A ⊆ Ω := by
    intro z hz
    exact ⟨hz.1,fun h => hz.2 (ball_subset_closedBall (hKinner h))⟩
  have hcinner : c ∈ closedBall d r := ball_subset_closedBall (hKinner hc)
  apply exists_primitive_of_outward_radial_anchors f G c Ω A
    (isOpen_ball.sdiff hKclosed) (isOpen_ball.sdiff isClosed_closedBall) hf hAΩ hG
  · intro z hz
    apply exists_outward_radialPoint_mem_annulus d c z r R hr hrR hz.1
    intro he
    subst z
    exact hz.2 hc
  · intro z hz v hv hp
    exact segment_radialPoint_subset_disc_compl d c z R v K hKstar hz hp.1 hv
  · intro z _ v u hv hu hpv hpu
    exact segment_radialPoints_subset_annulus d c z r R v u hcinner hv hu hpv hpu

/-- Zero inner period and holomorphy up to the outer circle supply an
actual primitive on the entire disc complement, rather than only its
outer annulus. -/
theorem exists_primitive_on_disc_complement_of_zero_period
    (f : ℂ → ℂ) (d c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (K : Set ℂ) (hKclosed : IsClosed K) (hc : c ∈ K) (hKstar : StarConvex ℝ c K)
    (hKinner : K ⊆ ball d r) (hf : AnalyticOnNhd ℂ f (closedBall d R \ K))
    (hperiod : (∮ w in C(d,r), f w) = 0) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball d R \ K, HasDerivAt F (f z) z := by
  have hAnn : closedBall d R \ ball d r ⊆ closedBall d R \ K := by
    intro z hz
    exact ⟨hz.1,fun h => hz.2 (hKinner h)⟩
  obtain ⟨G,hG⟩ := exists_primitive_on_annulus_of_zero_period f d r R hr hrR (hf.mono hAnn) hperiod
  have hΩ : ball d R \ K ⊆ closedBall d R \ K :=
    fun _ hz => ⟨ball_subset_closedBall hz.1,hz.2⟩
  obtain ⟨F,_,hF⟩ := exists_primitive_on_disc_complement_of_annular_primitive
    f G d c r R hr.le hrR K hKclosed hc hKstar hKinner (hf.mono hΩ) hG
  exact ⟨F,hF⟩

end NLS.ComplexAnalysis
