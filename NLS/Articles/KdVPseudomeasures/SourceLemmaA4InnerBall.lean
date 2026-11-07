import NLS.ComplexAnalysis.NearIdentityImageInverse

/-! Corrected Lemma A.4: the printed m/8 error on B_m gives an
analytic inverse on the image of the OPEN ball of radius 2m/3.
That image still contains the entire CLOSED half ball. -/
noncomputable section
open Set Metric Filter Topology NLS.ComplexAnalysis
open scoped NNReal
namespace NLS.Articles.KdVPseudomeasures
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem lemmaA4_inner_derivative_bound (f : E → E) (m : ℝ) (hm : 0 < m)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 m))
    (hb : ∀ x ∈ closedBall (0:E) m, ‖f x-x‖ ≤ m/8)
    (x : E) (hx : ‖x‖ ≤ 2*m/3) :
    ‖fderiv ℂ f x-ContinuousLinearMap.id ℂ E‖ ≤ (3/4:ℝ) := by
  let g : E → E := fun z => f z-z
  have hsub : ball x (m/3) ⊆ closedBall (0:E) m := by
    intro z hz
    have hzn : ‖z-x‖ < m/3 := by simpa only [mem_ball,dist_eq_norm] using hz
    have hn := norm_le_norm_sub_add z x
    rw [mem_closedBall,dist_zero_right]
    linarith
  have hxm : x ∈ closedBall (0:E) m := by rw [mem_closedBall,dist_zero_right]; linarith
  have hg : DifferentiableOn ℂ g (ball x (m/3)) := by
    intro z hz
    exact ((hf z (hsub hz)).differentiableAt.sub differentiableAt_id).differentiableWithinAt
  have hmaps : MapsTo g (ball x (m/3)) (closedBall (g x) (m/4)) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le (g z) (g x)).trans (by
      have hz' := hb z (hsub hz)
      have hx' := hb x hxm
      dsimp only [g]
      linarith)
  have hd := Complex.norm_fderiv_le_div_of_mapsTo_ball hg hmaps (by positivity : 0 < m/3)
  have he : fderiv ℂ g x=fderiv ℂ f x-ContinuousLinearMap.id ℂ E :=
    ((hf x hxm).differentiableAt.hasFDerivAt.sub (hasFDerivAt_id x)).fderiv
  rw [he] at hd
  exact hd.trans_eq (by field_simp [hm.ne'])

omit [CompleteSpace E] in
private theorem lemmaA4_error_lipschitz (f : E → E) (m : ℝ) (hm : 0 < m)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 m))
    (hb : ∀ x ∈ closedBall (0:E) m, ‖f x-x‖ ≤ m/8)
    (x y : E) (hx : ‖x‖ ≤ 2*m/3) (hy : ‖y‖ ≤ 2*m/3) :
    ‖(f x-x)-(f y-y)‖ ≤ (3/4:ℝ)*‖x-y‖ := by
  let g : E → E := fun z => f z-z
  have hxm (z : E) (hz : z ∈ closedBall (0:E) (2*m/3)) : z ∈ closedBall (0:E) m := by
    rw [mem_closedBall,dist_zero_right] at hz ⊢
    linarith
  have hd (z : E) (hz : z ∈ closedBall (0:E) (2*m/3)) : DifferentiableAt ℂ g z :=
    (hf z (hxm z hz)).differentiableAt.sub differentiableAt_id
  have hder (z : E) (hz : z ∈ closedBall (0:E) (2*m/3)) : ‖fderiv ℂ g z‖ ≤ (3/4:ℝ) := by
    have he : fderiv ℂ g z=fderiv ℂ f z-ContinuousLinearMap.id ℂ E :=
      ((hf z (hxm z hz)).differentiableAt.hasFDerivAt.sub (hasFDerivAt_id z)).fderiv
    rw [he]
    exact lemmaA4_inner_derivative_bound f m hm hf hb z (by simpa only [mem_closedBall,dist_zero_right] using hz)
  exact (convex_closedBall (0:E) (2*m/3)).norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℂ) (f := g) hd hder
    (by simpa only [mem_closedBall,dist_zero_right] using hy)
    (by simpa only [mem_closedBall,dist_zero_right] using hx)

private theorem lemmaA4_derivative_bijective (T : E →L[ℂ] E)
    (hT : ‖T-ContinuousLinearMap.id ℂ E‖ ≤ (3/4:ℝ)) : Function.Bijective T := by
  have hn : ‖(1 : E →L[ℂ] E)-T‖ < 1 := by
    change ‖ContinuousLinearMap.id ℂ E-T‖ < 1
    rw [norm_sub_rev]
    exact hT.trans_lt (by norm_num)
  have hu := isUnit_one_sub_of_norm_lt_one hn
  have he : (1 : E →L[ℂ] E)-(1-T)=T := by abel
  rw [he] at hu
  exact ContinuousLinearMap.isUnit_iff_bijective.mp hu

theorem sourceLemmaA_4_innerBall (f : E → E) (m : ℝ) (hm : 0 < m)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 m))
    (hb : ∀ x ∈ closedBall (0:E) m, ‖f x-x‖ ≤ m/8) :
    ∃ g : E → E,
      IsOpen (f '' ball 0 (2*m/3)) ∧ AnalyticOnNhd ℂ g (f '' ball 0 (2*m/3)) ∧
      Set.InjOn f (closedBall (0:E) (2*m/3)) ∧
      closedBall (0:E) (m/2) ⊆ f '' ball 0 (2*m/3) ∧
      (∀ x ∈ ball (0:E) (2*m/3), g (f x)=x) ∧
      ∀ y ∈ f '' ball (0:E) (2*m/3), g y ∈ ball 0 (2*m/3) ∧ f (g y)=y := by
  classical
  have hLip := lemmaA4_error_lipschitz f m hm hf hb
  have hinj : Set.InjOn f (closedBall (0:E) (2*m/3)) := by
    intro x hx y hy hxy
    have hh := hLip x y (by simpa only [mem_closedBall,dist_zero_right] using hx)
      (by simpa only [mem_closedBall,dist_zero_right] using hy)
    rw [hxy,show (f y-x)-(f y-y)= -(x-y) by abel,norm_neg] at hh
    have hz : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hfU : AnalyticOnNhd ℂ f (ball 0 (2*m/3)) := hf.mono (by
    intro x hx
    rw [mem_ball_zero_iff] at hx
    rw [mem_closedBall,dist_zero_right]
    linarith)
  have hbij (x : E) (hx : x ∈ ball (0:E) (2*m/3)) : Function.Bijective (fderiv ℂ f x) :=
    lemmaA4_derivative_bijective _ (lemmaA4_inner_derivative_bound f m hm hf hb x (mem_ball_zero_iff.mp hx).le)
  obtain ⟨g,hopen,hA,hleft,hright⟩ := exists_analytic_inverse_on_injective_open_image f
    (ball 0 (2*m/3)) isOpen_ball hfU (hinj.mono ball_subset_closedBall) hbij
  refine ⟨g,hopen,hA,hinj,?_,hleft,hright⟩
  intro y hy
  have hyn : ‖y‖ ≤ m/2 := by simpa only [mem_closedBall,dist_zero_right] using hy
  let Φ : E → E := fun x => y-(f x-x)
  have hmap : MapsTo Φ (closedBall (0:E) (2*m/3)) (closedBall (0:E) (2*m/3)) := by
    intro x hx
    have hxn : ‖x‖ ≤ 2*m/3 := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hxm : x ∈ closedBall (0:E) m := by rw [mem_closedBall,dist_zero_right]; linarith
    rw [mem_closedBall,dist_zero_right]
    exact (norm_sub_le y (f x-x)).trans (by linarith [hb x hxm])
  let F : closedBall (0:E) (2*m/3) → closedBall (0:E) (2*m/3) := fun x => ⟨Φ x,hmap x.property⟩
  have hc : ContractingWith (3/4:ℝ≥0) F := by
    refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro x z
    change dist (Φ x.val) (Φ z.val) ≤ ((3/4:ℝ≥0):ℝ)*dist x.val z.val
    rw [show ((3/4:ℝ≥0):ℝ)=(3/4:ℝ) by norm_num,dist_eq_norm,dist_eq_norm,
      show Φ x.val-Φ z.val= -((f x.val-x.val)-(f z.val-z.val)) by dsimp only [Φ]; abel,norm_neg]
    exact hLip x.val z.val
      (by simpa only [mem_closedBall,dist_zero_right] using x.property)
      (by simpa only [mem_closedBall,dist_zero_right] using z.property)
  let : Nonempty (closedBall (0:E) (2*m/3)) := ⟨⟨0,mem_closedBall_self (by positivity)⟩⟩
  let : CompleteSpace (closedBall (0:E) (2*m/3)) := isClosed_closedBall.completeSpace_coe
  let x := hc.fixedPoint F
  have hfix : Φ x.val=x.val := congrArg Subtype.val hc.fixedPoint_isFixedPt
  have hfx : f x.val=y := by
    dsimp only [Φ] at hfix
    calc
      f x.val=x.val+(f x.val-x.val) := by abel
      _ = y := (sub_eq_iff_eq_add.mp hfix).symm
  have hxm : x.val ∈ closedBall (0:E) m := by
    have hxn : ‖x.val‖ ≤ 2*m/3 := by simpa only [mem_closedBall,dist_zero_right] using x.property
    rw [mem_closedBall,dist_zero_right]
    linarith
  have hsmall := hb x.val hxm
  rw [hfx] at hsmall
  have hxinner : ‖x.val‖ < 2*m/3 := by
    have hh := norm_le_norm_sub_add x.val y
    rw [norm_sub_rev] at hh
    linarith
  exact ⟨x.val,mem_ball_zero_iff.mpr hxinner,hfx⟩

end NLS.Articles.KdVPseudomeasures
