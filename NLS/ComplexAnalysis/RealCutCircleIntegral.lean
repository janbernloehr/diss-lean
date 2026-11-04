import NLS.ComplexAnalysis.RealGapEllipseLimit
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # A circle integral as the integral of a real-cut jump -/

noncomputable section
open Set Metric Complex Filter
open scoped unitInterval Topology
namespace NLS.ComplexAnalysis

/-- A continuous extension of a square bounds either branch uniformly
on the complement of its cut in a compact set. -/
theorem exists_norm_bound_of_continuous_square_on_compact
    (f g : ℂ → ℂ) (K T : Set ℂ) (hK : IsCompact K) (hg : ContinuousOn g K)
    (hsq : ∀ z ∈ K \ T, f z ^ 2 = g z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K \ T, ‖f z‖ ≤ M := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨B + 1, by positivity, fun z hz => ?_⟩
  have hnorm : ‖f z‖ ^ 2 = ‖g z‖ := by rw [← norm_pow, hsq z hz]
  have hbound : ‖g z‖ ≤ B := (hC z hz.1).trans (le_max_left _ _)
  nlinarith [norm_nonneg (f z), sq_nonneg B]

/-- A bounded holomorphic function on a disc with a real segment removed
has circle integral equal to minus the left-to-right integral of its
upper-minus-lower jump. The proof uses a smooth shrinking contour and
dominated convergence, including control near both endpoints. -/
theorem circleIntegral_eq_neg_real_cut_jump
    (f : ℂ → ℂ) (lower upper : ℝ → ℂ) (c d r R M : ℝ)
    (hd : 0 < d) (hdr : d < r) (hrR : r < R) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f
      (ball (c : ℂ) R \ segment ℝ ((c - d : ℝ) : ℂ) ((c + d : ℝ) : ℂ)))
    (hbound : ∀ z ∈ closedBall (c : ℂ) r \
        segment ℝ ((c - d : ℝ) : ℂ) ((c + d : ℝ) : ℂ), ‖f z‖ ≤ M)
    (hlcont : ContinuousOn lower (Icc (c - d) (c + d)))
    (hucont : ContinuousOn upper (Icc (c - d) (c + d)))
    (hlower : ∀ x ∈ Icc (c - d) (c + d),
      Tendsto f (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (lower x)))
    (hupper : ∀ x ∈ Icc (c - d) (c + d),
      Tendsto f (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (upper x))) :
    (∮ z in C((c : ℂ), r), f z) =
      -(∫ x in (c - d)..(c + d), upper x - lower x) := by
  let K := segment ℝ ((c - d : ℝ) : ℂ) ((c + d : ℝ) : ℂ)
  let ε₀ := (r - d) / 2
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; linarith
  have hKclosed : IsClosed K := by
    dsimp only [K]
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hopen : IsOpen (ball (c : ℂ) R \ K) := isOpen_ball.sdiff hKclosed
  have hsize (ε : ℝ) (hε : ε ∈ Ioo 0 ε₀) : d + ε < r := by
    dsimp [ε₀] at hε
    linarith [hε.2]
  have hmem (ε : ℝ) (hε : ε ∈ Ioo 0 ε₀) (θ : ℝ) :
      realGapEllipse c d ε θ ∈ closedBall (c : ℂ) r \ K := by
    exact ⟨closedBall_subset_closedBall (hsize ε hε).le
      (realGapEllipse_mem_closedBall c d ε θ hd.le hε.1.le),
      realGapEllipse_not_mem_segment c d ε θ hd hε.1⟩
  have hcont (ε : ℝ) (hε : ε ∈ Ioo 0 ε₀) :
      Continuous (fun θ => f (realGapEllipse c d ε θ)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    apply (hf _ ⟨closedBall_subset_ball hrR (hmem ε hε θ).1,
      (hmem ε hε θ).2⟩).continuousAt.comp
    unfold realGapEllipse
    fun_prop
  have hlimit := tendsto_curveIntegral_realGapEllipse f lower upper c d ε₀ M
    hd.le hε₀ hM hcont (fun ε hε θ _ => hbound _ (hmem ε hε θ))
    hlcont hucont hlower hupper
  have hcircle (ε : ℝ) (hε : ε ∈ Ioo 0 ε₀) :
      (∮ z in C((c : ℂ), r), f z) = ∮ z in C((c : ℂ), d + ε), f z := by
    have hK : K ⊆ ball (c : ℂ) (d + ε) := by
      apply (convex_ball _ _).segment_subset
      · simp only [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
        rw [show c - d - c = -d by ring, abs_neg, abs_of_pos hd]
        linarith [hε.1]
      · simp only [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
        rw [show c + d - c = d by ring, abs_of_pos hd]
        linarith [hε.1]
    have ha : AnalyticOnNhd ℂ f (closedBall (c : ℂ) r \ ball (c : ℂ) (d + ε)) := by
      intro z hz
      exact hf z ⟨closedBall_subset_ball hrR hz.1, fun hk => hz.2 (hK hk)⟩
    exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (by linarith [hε.1]) (hsize ε hε).le countable_empty ha.continuousOn
      (fun z hz => (ha z ⟨ball_subset_closedBall hz.1.1,
        fun hb => hz.1.2 (ball_subset_closedBall hb)⟩).differentiableAt)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 ε₀ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds hε₀)] with ε hε hε₀'
    exact ⟨hε, hε₀'⟩
  have hconstant : Tendsto
      (fun ε => ∫ᶜ z in realGapEllipsePath c d ε, holomorphicOneForm f z)
      (𝓝[>] 0) (𝓝 (-(∮ z in C((c : ℂ), r), f z))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hsmall] with ε hε
    exact (curveIntegral_realGapEllipse_eq_neg_circleIntegral f c d ε R hd hε.1
      ((hsize ε hε).trans hrR) hf.differentiableOn).trans
      (congrArg Neg.neg (hcircle ε hε).symm) |>.symm
  have heq := tendsto_nhds_unique hconstant hlimit
  exact neg_eq_iff_eq_neg.mp heq

end NLS.ComplexAnalysis
