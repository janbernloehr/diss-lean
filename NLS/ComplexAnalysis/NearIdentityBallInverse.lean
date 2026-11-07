import NLS.ComplexAnalysis.NearIdentityAnalyticInverse
import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Complex.Schwarz

/-! Analytic inversion on a ball from a uniform bound on the actual error. -/
noncomputable section
open Set Metric Filter Topology
open scoped NNReal
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A uniform m/32 error on the double ball implies the source derivative
bound 1/16, including every point of the closed inner ball. -/
theorem norm_fderiv_sub_id_le_of_ball_error (f : E → E) (m : ℝ) (hm : 0 < m)
    (hf : AnalyticOnNhd ℂ f (ball 0 (2*m)))
    (hb : ∀ x ∈ ball (0:E) (2*m), ‖f x-x‖ ≤ m/32)
    (x : E) (hx : ‖x‖ ≤ m) :
    ‖fderiv ℂ f x-ContinuousLinearMap.id ℂ E‖ ≤ (1/16 : ℝ) := by
  let g : E → E := fun z => f z-z
  have hsub : ball x m ⊆ ball (0:E) (2*m) := by
    intro z hz
    have hzn : ‖z-x‖ < m := by simpa only [mem_ball, dist_eq_norm] using hz
    have hn := norm_le_norm_sub_add z x
    rw [mem_ball_zero_iff]
    linarith
  have hx2 : x ∈ ball (0:E) (2*m) := by rw [mem_ball_zero_iff]; linarith
  have hg : DifferentiableOn ℂ g (ball x m) := by
    intro z hz
    exact ((hf z (hsub hz)).differentiableAt.sub differentiableAt_id).differentiableWithinAt
  have hmaps : MapsTo g (ball x m) (closedBall (g x) (m/16)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le (g z) (g x)).trans (by
      have hz' := hb z (hsub hz)
      have hx' := hb x hx2
      dsimp [g]
      linarith)
  have hder := Complex.norm_fderiv_le_div_of_mapsTo_ball hg hmaps hm
  have he : fderiv ℂ g x = fderiv ℂ f x-ContinuousLinearMap.id ℂ E :=
    ((hf x hx2).differentiableAt.hasFDerivAt.sub (hasFDerivAt_id x)).fderiv
  rw [he] at hder
  exact hder.trans_eq (by field_simp [hm.ne'])

omit [CompleteSpace E] in
/-- The actual error is Lipschitz on the whole closed inner ball. -/
theorem norm_error_sub_le_of_ball_error (f : E → E) (m : ℝ) (hm : 0 < m)
    (hf : AnalyticOnNhd ℂ f (ball 0 (2*m)))
    (hb : ∀ x ∈ ball (0:E) (2*m), ‖f x-x‖ ≤ m/32)
    (x y : E) (hx : ‖x‖ ≤ m) (hy : ‖y‖ ≤ m) :
    ‖(f x-x)-(f y-y)‖ ≤ (1/16 : ℝ)*‖x-y‖ := by
  let g : E → E := fun z => f z-z
  have hd (z : E) (hz : z ∈ closedBall (0:E) m) : DifferentiableAt ℂ g z := by
    have hzn : ‖z‖ ≤ m := by simpa only [mem_closedBall, dist_zero_right] using hz
    exact (hf z (by rw [mem_ball_zero_iff]; linarith)).differentiableAt.sub differentiableAt_id
  have hder (z : E) (hz : z ∈ closedBall (0:E) m) : ‖fderiv ℂ g z‖ ≤ (1/16 : ℝ) := by
    have hzn : ‖z‖ ≤ m := by simpa only [mem_closedBall, dist_zero_right] using hz
    have he : fderiv ℂ g z = fderiv ℂ f z-ContinuousLinearMap.id ℂ E :=
      ((hf z (by rw [mem_ball_zero_iff]; linarith)).differentiableAt.hasFDerivAt.sub (hasFDerivAt_id z)).fderiv
    rw [he]
    exact norm_fderiv_sub_id_le_of_ball_error f m hm hf hb z hzn
  exact (convex_closedBall (0:E) m).norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℂ) (f := g) hd hder
    (by simpa only [mem_closedBall, dist_zero_right] using hy)
    (by simpa only [mem_closedBall, dist_zero_right] using hx)

/-- The double-ball error bound gives an analytic inverse on a target ball
strictly larger than the closed half ball. Source injectivity and both inverse
identities are actual conclusions, rather than assumed invertibility. -/
theorem exists_analytic_inverse_of_ball_error (f : E → E) (m : ℝ) (hm : 0 < m)
    (hf : AnalyticOnNhd ℂ f (ball 0 (2*m)))
    (hb : ∀ x ∈ ball (0:E) (2*m), ‖f x-x‖ ≤ m/32) :
    ∃ g : E → E,
      AnalyticOnNhd ℂ g (ball 0 (3*m/4)) ∧
      Set.InjOn f (closedBall (0:E) m) ∧
      (∀ y : E, ‖y‖ ≤ 3*m/4 → g y ∈ ball 0 m ∧ f (g y) = y) ∧
      ∀ x : E, ‖x‖ ≤ m → ‖f x‖ ≤ 3*m/4 → g (f x) = x := by
  classical
  have hLip := norm_error_sub_le_of_ball_error f m hm hf hb
  have hinj : Set.InjOn f (closedBall (0:E) m) := by
    intro x hx y hy hxy
    have hxn : ‖x‖ ≤ m := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hyn : ‖y‖ ≤ m := by simpa only [mem_closedBall, dist_zero_right] using hy
    have hh := hLip x y hxn hyn
    rw [hxy, show (f y-x)-(f y-y) = -(x-y) by abel, norm_neg] at hh
    have hz : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hex (y : E) (hy : ‖y‖ ≤ 3*m/4) : ∃ x ∈ ball (0:E) m, f x = y := by
    let Φ : E → E := fun x => y-(f x-x)
    have hmap : MapsTo Φ (closedBall (0:E) m) (closedBall (0:E) m) := by
      intro x hx
      have hxn : ‖x‖ ≤ m := by simpa only [mem_closedBall, dist_zero_right] using hx
      have hx2 : x ∈ ball (0:E) (2*m) := by rw [mem_ball_zero_iff]; linarith
      rw [mem_closedBall, dist_zero_right]
      exact (norm_sub_le y (f x-x)).trans (by linarith [hb x hx2])
    let F : closedBall (0:E) m → closedBall (0:E) m := fun x => ⟨Φ x, hmap x.property⟩
    have hc : ContractingWith (1/16 : ℝ≥0) F := by
      refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
      intro x z
      change dist (Φ x.val) (Φ z.val) ≤ ((1/16:ℝ≥0):ℝ)*dist x.val z.val
      rw [show ((1/16:ℝ≥0):ℝ) = (1/16:ℝ) by norm_num, dist_eq_norm, dist_eq_norm,
        show Φ x.val-Φ z.val = -((f x.val-x.val)-(f z.val-z.val)) by dsimp [Φ]; abel,
        norm_neg]
      exact hLip x.val z.val
        (by simpa only [mem_closedBall, dist_zero_right] using x.property)
        (by simpa only [mem_closedBall, dist_zero_right] using z.property)
    let : Nonempty (closedBall (0:E) m) := ⟨⟨0, mem_closedBall_self hm.le⟩⟩
    let : CompleteSpace (closedBall (0:E) m) := isClosed_closedBall.completeSpace_coe
    let x := hc.fixedPoint F
    have hfix : Φ x.val = x.val := congrArg Subtype.val hc.fixedPoint_isFixedPt
    have hfx : f x.val = y := by
      dsimp [Φ] at hfix
      calc
        f x.val = x.val+(f x.val-x.val) := by abel
        _ = y := (sub_eq_iff_eq_add.mp hfix).symm
    have hxn : ‖x.val‖ ≤ m := by simpa only [mem_closedBall, dist_zero_right] using x.property
    have hx2 : x.val ∈ ball (0:E) (2*m) := by rw [mem_ball_zero_iff]; linarith
    have hsmall := hb x.val hx2
    rw [hfx] at hsmall
    have hstrict : ‖x.val‖ < m := by
      have hh := norm_le_norm_sub_add x.val y
      rw [norm_sub_rev] at hh
      linarith
    exact ⟨x.val, mem_ball_zero_iff.mpr hstrict, hfx⟩
  let g (y : E) : E := if h : ∃ x ∈ ball (0:E) m, f x = y then Classical.choose h else 0
  have hspec (y : E) (hy : ‖y‖ ≤ 3*m/4) : g y ∈ ball (0:E) m ∧ f (g y) = y := by
    have hh := hex y hy
    dsimp only [g]
    rw [dif_pos hh]
    exact Classical.choose_spec hh
  refine ⟨g, ?_, hinj, hspec, ?_⟩
  · intro y hy
    obtain ⟨hgmem, hfg⟩ := hspec y (mem_ball_zero_iff.mp hy).le
    have hgn : ‖g y‖ ≤ m := (mem_ball_zero_iff.mp hgmem).le
    have hg2 : g y ∈ ball (0:E) (2*m) := by rw [mem_ball_zero_iff]; linarith
    have hnear := norm_fderiv_sub_id_le_of_ball_error f m hm hf hb (g y) hgn
    obtain ⟨e, he, _⟩ := exists_continuousLinearEquiv_of_norm_sub_id_le_half
      (fderiv ℂ f (g y)) (hnear.trans (by norm_num))
    let H : E × E → E := fun t => f t.1-t.2
    have hff : AnalyticAt ℂ (fun t : E × E => f t.1) (g y,y) :=
      (hf (g y) hg2).comp (f := fun t : E × E => t.1) analyticAt_fst
    have hH : AnalyticAt ℂ H (g y,y) := hff.sub analyticAt_snd
    have hder : (fderiv ℂ H (g y,y)).comp (ContinuousLinearMap.inl ℂ E E) = fderiv ℂ f (g y) := by
      have hh := (((hf (g y) hg2).differentiableAt.hasFDerivAt.comp (g y,y)
        (hasFDerivAt_fst (𝕜 := ℂ) (p := (g y,y)))).sub (hasFDerivAt_snd (𝕜 := ℂ) (p := (g y,y)))).fderiv
      change (fderiv ℂ (f ∘ Prod.fst-Prod.snd) (g y,y)).comp (ContinuousLinearMap.inl ℂ E E) = _
      rw [hh]
      ext z
      simp
    have hbij : Function.Bijective ((fderiv ℂ H (g y,y)).comp (ContinuousLinearMap.inl ℂ E E)) := by
      rw [hder, ← he]
      exact e.bijective
    obtain ⟨s, hs, hsy, hroot⟩ := exists_analytic_implicitBanachRoot H (g y) y hH
      (by dsimp [H]; rw [hfg, sub_self]) hbij
    have hsball : ∀ᶠ z in 𝓝 y, s z ∈ ball (0:E) m :=
      hs.continuousAt.eventually (by rw [hsy]; exact isOpen_ball.mem_nhds hgmem)
    apply hs.congr
    filter_upwards [hroot, hsball, isOpen_ball.mem_nhds hy] with z hz hsz hzball
    have hg := hspec z (mem_ball_zero_iff.mp hzball).le
    apply hinj (ball_subset_closedBall hsz) (ball_subset_closedBall hg.1)
    dsimp [H] at hz
    exact (sub_eq_zero.mp hz).trans hg.2.symm
  · intro x hx hfx
    have hg := hspec (f x) hfx
    exact hinj (ball_subset_closedBall hg.1)
      (by simpa only [mem_closedBall, dist_zero_right] using hx) hg.2

end NLS.ComplexAnalysis
