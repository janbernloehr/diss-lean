import NLS.KdV.HillHminusOneHalfPlaneSheets
import NLS.KdV.HillHminusOneMomentCutRoot
import NLS.ComplexAnalysis.SignedSquareBoundary

/-! # Physical normalization of real H^-1 Hill cut roots

The sign fixed on one enclosing circle agrees with the actual primitive
throughout both half-discs. The filled primitive square has real boundary
values even where the source primitive itself is not defined.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV

theorem hillHminus_filled_square_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (n : ℕ+) (c R x : ℝ) (K : ℂ → ℂ)
    (hK : AnalyticOnNhd ℂ K (ball (c : ℂ) R))
    (hx : (x : ℂ) ∈ ball (c : ℂ) R)
    (hmatch : ∀ z ∈ ball (c : ℂ) R, z.im ≠ 0 →
      K z = (hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^2) :
    (K (x : ℂ)).im = 0 := by
  apply im_eq_zero_of_continuous_reflection_upper K x (hK _ hx).continuousAt
  have hb : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ), z ∈ ball (c : ℂ) R :=
    nhdsWithin_le_nhds (isOpen_ball.mem_nhds hx)
  filter_upwards [hb,self_mem_nhdsWithin] with z hz hi
  have hzc : conj z ∈ ball (c : ℂ) R := by
    simpa only [mem_ball,dist_conj_comm,conj_ofReal] using hz
  rw [hmatch z hz hi.ne',hmatch (conj z) hzc (by simpa only [conj_im,neg_ne_zero] using hi.ne'),
    hillHminusContinuedPrimitive_conj q hq z
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hq z hi.ne')]
  simp only [map_pow,map_add,map_mul,map_natCast,conj_ofReal,conj_I]
  ring

/-- One sign on the complete contour selects the physical branch on
both half-discs; the two components are anchored separately. -/
theorem exists_hillHminus_physical_cut_sign
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (n : ℕ+) (c l u R : ℝ) (K B : ℂ → ℂ)
    (hR : 0 < R) (hl : (l : ℂ) ∈ ball (c : ℂ) (R/32))
    (hu : (u : ℂ) ∈ ball (c : ℂ) (R/32))
    (hB : AnalyticOnNhd ℂ B (ball (c : ℂ) R \ segment ℝ (l : ℂ) (u : ℂ)))
    (hsq : ∀ z ∈ ball (c : ℂ) R \ segment ℝ (l : ℂ) (u : ℂ), B z ≠ 0 ∧ B z^2 = K z)
    (hmatch : ∀ z ∈ closedBall (c : ℂ) R, (z,q) ∈ hillHminusContinuationDomain →
      K z = (hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^2)
    (hsource : ∀ z ∈ sphere (c : ℂ) (R/4), (z,q) ∈ hillHminusContinuationDomain) :
    ∃ k : ℂ, (k = 1 ∨ k = -1) ∧
      (∀ z ∈ sphere (c : ℂ) (R/4),
        k*B z = hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi) ∧
      (∀ z ∈ ball (c : ℂ) R, 0 < z.im → 0 < (k*B z).re) ∧
      (∀ z ∈ ball (c : ℂ) R, z.im < 0 → (k*B z).re < 0) := by
  let F : ℂ → ℂ := fun z => hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi
  let D := ball (c : ℂ) R \ segment ℝ (l : ℂ) (u : ℂ)
  have hseg : segment ℝ (l : ℂ) (u : ℂ) ⊆ ball (c : ℂ) (R/32) :=
    (convex_ball _ _).segment_subset hl hu
  have hcircle (z : ℂ) (hz : z ∈ sphere (c : ℂ) (R/4)) : z ∈ D := by
    refine ⟨sphere_subset_ball (by linarith) hz,?_⟩
    intro hs
    have hb := mem_ball.mp (hseg hs)
    have he := mem_sphere.mp hz
    linarith
  have hFc : AnalyticOnNhd ℂ F (sphere (c : ℂ) (R/4)) := by
    intro z hz
    exact ((analyticOnNhd_hillHminusContinuedPrimitive _ (hsource z hz)).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)).add analyticAt_const
  have heq (z : ℂ) (hz : z ∈ sphere (c : ℂ) (R/4)) : F z^2 = B z^2 :=
    (hmatch z (closedBall_subset_closedBall (by linarith : R/4 ≤ R) (sphere_subset_closedBall hz)) (hsource z hz)).symm.trans
      (hsq z (hcircle z hz)).2.symm
  obtain ⟨k,hk,hFB⟩ := exists_fixed_sign_of_sq_eq_on_preconnected F B (sphere (c : ℂ) (R/4))
    (isPreconnected_sphere (by simp) _ _) hFc.continuousOn (hB.mono hcircle).continuousOn heq
    (fun z hz => (hsq z (hcircle z hz)).1)
  have hk2 : k^2 = 1 := by rcases hk with rfl | rfl <;> norm_num
  have hkne : k ≠ 0 := by intro he; rw [he] at hk2; norm_num at hk2
  have hside (S : Set ℂ) (hS : IsPreconnected S) (hsub : S ⊆ D)
      (him : ∀ z ∈ S, z.im ≠ 0) (w : ℂ) (hw : w ∈ S)
      (hwc : w ∈ sphere (c : ℂ) (R/4)) : EqOn F (fun z => k*B z) S := by
    have hF : AnalyticOnNhd ℂ F S := by
      intro z hz
      exact ((analyticOnNhd_hillHminusContinuedPrimitive _
        (mem_hillHminusContinuationDomain_of_im_ne_zero q hq z (him z hz))).comp
          (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)).add analyticAt_const
    apply hS.eq_of_sq_eq hF.continuousOn
      (continuousOn_const.mul (hB.mono hsub).continuousOn) ?_ ?_ hw (hFB w hwc)
    · intro z hz
      change F z^2 = (k*B z)^2
      rw [mul_pow,hk2,one_mul]
      exact (hmatch z (ball_subset_closedBall (hsub hz).1)
        (mem_hillHminusContinuationDomain_of_im_ne_zero q hq z (him z hz))).symm.trans
          (hsq z (hsub hz)).2.symm
    · intro z hz he
      exact mul_ne_zero hkne (hsq z (hsub hz)).1 he
  have hplus : EqOn F (fun z => k*B z) (ball (c : ℂ) R ∩ {z : ℂ | 0 < z.im}) := by
    refine hside _ ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
      (fun z hz => ⟨hz.1,not_mem_real_segment_of_im_ne_zero l u z hz.2.ne'⟩)
      (fun _ hz => hz.2.ne') ((c : ℂ)+I*(R/4 : ℝ)) ?_ ?_
    · constructor
      · simp only [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_mul,norm_I,one_mul,
          norm_real,Real.norm_eq_abs,abs_of_pos (show 0 < R/4 by positivity)]
        linarith
      · simp only [mem_ofPred_eq,add_im,ofReal_im,mul_im,I_re,zero_mul,I_im,ofReal_re,one_mul,zero_add]
        positivity
    · simp only [mem_sphere,dist_eq_norm,add_sub_cancel_left,norm_mul,norm_I,one_mul,
        norm_real,Real.norm_eq_abs,abs_of_pos (show 0 < R/4 by positivity)]
  have hminus : EqOn F (fun z => k*B z) (ball (c : ℂ) R ∩ {z : ℂ | z.im < 0}) := by
    refine hside _ ((convex_ball _ _).inter (convex_halfSpace_im_lt 0)).isPreconnected
      (fun z hz => ⟨hz.1,not_mem_real_segment_of_im_ne_zero l u z hz.2.ne⟩)
      (fun _ hz => hz.2.ne) ((c : ℂ)-I*(R/4 : ℝ)) ?_ ?_
    · constructor
      · simp only [mem_ball,dist_eq_norm,sub_sub_cancel_left,norm_neg,norm_mul,norm_I,one_mul,
          norm_real,Real.norm_eq_abs,abs_of_pos (show 0 < R/4 by positivity)]
        linarith
      · simp only [mem_ofPred_eq,sub_im,ofReal_im,mul_im,I_re,zero_mul,I_im,ofReal_re,one_mul,zero_add]
        linarith
    · simp only [mem_sphere,dist_eq_norm,sub_sub_cancel_left,norm_neg,norm_mul,norm_I,one_mul,
        norm_real,Real.norm_eq_abs,abs_of_pos (show 0 < R/4 by positivity)]
  refine ⟨k,hk,fun z hz => (hFB z hz).symm,?_,?_⟩
  · intro z hz hi
    have he : F z = k*B z := hplus ⟨hz,hi⟩
    rw [← he]
    simpa [F] using hillHminusContinuedPrimitive_re_pos q hq z hi
  · intro z hz hi
    have he : F z = k*B z := hminus ⟨hz,hi⟩
    rw [← he]
    simpa [F] using hillHminusContinuedPrimitive_re_neg q hq z hi

end NLS.KdV
