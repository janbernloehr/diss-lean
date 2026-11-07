import NLS.Articles.KdVConvexity.ActionTaylorAtZero
import NLS.SequenceSpaces.HilbertStrictConcavity

/-! # Uniform Hessian bounds in the original positive-index Hilbert space -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVConvexity

def actionBilinearPairing (v w : ActionSpace) : ℂ :=
  Coeff.dualPairing (actionReindex v) (actionReindex w)

theorem actionBilinearPairing_eq_tsum (v w : ActionSpace) :
    actionBilinearPairing v w=∑' n : ℕ+, v n*w n := by
  rw [actionBilinearPairing,Coeff.dualPairing_apply]
  simpa only [actionReindex_apply] using actionIndexEquiv.tsum_eq (fun n : ℕ+ => v n*w n)

theorem norm_actionBilinearPairing_le (v w : ActionSpace) :
    ‖actionBilinearPairing v w‖ ≤ ‖v‖*‖w‖ := by
  simpa only [actionBilinearPairing,actionReindex.norm_map] using Coeff.norm_dualPairing_le (actionReindex v) (actionReindex w)

theorem actionBilinearPairing_cotangent (L : ActionSpace →L[ℂ] ℂ) (v : ActionSpace) :
    actionBilinearPairing (actionCotangentCoefficients L) v=L v := by
  change Coeff.dualPairing (actionReindex (actionUnreindex
    (Coeff.hilbertCotangentCoefficients (L.comp actionUnreindex.toContinuousLinearMap)))) (actionReindex v)=_
  rw [actionReindex_actionUnreindex,Coeff.dualPairing_hilbertCotangentCoefficients]
  change L (actionUnreindex (actionReindex v))=L v
  rw [actionUnreindex_actionReindex]

theorem action_hessian_eq_pairing_gradient_derivative
    (H : ActionSpace → ℂ) (a : ActionSpace) (hH : AnalyticAt ℂ H a) (v w : ActionSpace) :
    fderiv ℂ (fderiv ℂ H) a v w=actionBilinearPairing (fderiv ℂ (actionGradient H) a v) w := by
  have hd := (actionCotangentCoefficients.hasFDerivAt.comp a
    hH.fderiv.differentiableAt.hasFDerivAt).fderiv
  have he : fderiv ℂ (actionGradient H) a v=actionCotangentCoefficients (fderiv ℂ (fderiv ℂ H) a v) :=
    congrArg (fun L : ActionSpace →L[ℂ] ActionSpace => L v) hd
  rw [he,actionBilinearPairing_cotangent]

theorem actionBilinearPairing_real_self (v : ActionSpace) (hv : ∀ n : ℕ+, (v n).im=0) :
    actionBilinearPairing v v=((‖v‖^2 : ℝ) : ℂ) := by
  let J := Coeff.reCLM 2 (actionReindex v)
  have hJ : RealCoeff.complexCLM 2 J=actionReindex v :=
    RealCoeff.complexCLM_reCLM 2 _ (fun k => hv (actionIndexEquiv k))
  have hn : ‖J‖=‖v‖ := by
    rw [←Coeff.norm_real_hilbert_inclusion J,hJ,actionReindex.norm_map]
  have h := Coeff.dualPairing_real_self J
  rw [hJ,hn] at h
  exact h

/-- One radius works for EVERY real Hilbert direction, including infinite
support, at EVERY complex action in the ball. -/
theorem exists_action_ball_hessian_bound
    (H : ActionSpace → ℂ) (V : Set ActionSpace) (hV : IsOpen V)
    (h0 : (0 : ActionSpace) ∈ V) (hH : AnalyticOnNhd ℂ H V)
    (hd0 : fderiv ℂ (actionGradient H) 0=(-6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace) :
    ∃ r : ℝ, 0<r ∧ ball (0 : ActionSpace) r ⊆ V ∧
      ∀ a ∈ ball (0 : ActionSpace) r, ∀ v : ActionSpace, (∀ n : ℕ+, (v n).im=0) →
        (fderiv ℂ (fderiv ℂ H) a v v).re ≤ -‖v‖^2 := by
  have hG := analyticOnNhd_actionGradient H hH
  have hclose := (hG.fderiv 0 h0).continuousAt.eventually
    (ball_mem_nhds (fderiv ℂ (actionGradient H) 0) (by norm_num : (0 : ℝ)<3))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hV.mem_nhds h0) hclose)
  refine ⟨r,hr,fun a ha => (hball ha).1,?_⟩
  intro a ha v hv
  let L := fderiv ℂ (actionGradient H) a-fderiv ℂ (actionGradient H) 0
  have hL : ‖L‖ ≤ 3 := (show ‖L‖<3 from by
    simpa only [L,dist_eq_norm,Set.mem_ofPred_eq] using! (hball ha).2).le
  have hb : ‖actionBilinearPairing (L v) v‖ ≤ 3*‖v‖^2 := by
    calc
      ‖actionBilinearPairing (L v) v‖ ≤ ‖L v‖*‖v‖ := norm_actionBilinearPairing_le _ _
      _ ≤ (‖L‖*‖v‖)*‖v‖ := mul_le_mul_of_nonneg_right (L.le_opNorm v) (norm_nonneg _)
      _ ≤ (3*‖v‖)*‖v‖ := by gcongr
      _ = _ := by ring
  have he : fderiv ℂ (actionGradient H) a v=L v+(-6 : ℂ) • v := by simp [L,hd0]
  have hess : fderiv ℂ (fderiv ℂ H) a v v=actionBilinearPairing (L v) v-6*((‖v‖^2 : ℝ) : ℂ) := by
    rw [action_hessian_eq_pairing_gradient_derivative H a (hH a (hball ha).1),he]
    simp only [actionBilinearPairing,map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
    rw [show Coeff.dualPairing (actionReindex v) (actionReindex v)=((‖v‖^2 : ℝ) : ℂ)
      from actionBilinearPairing_real_self v hv]
    ring
  have hreal := (Complex.re_le_norm (actionBilinearPairing (L v) v)).trans hb
  rw [hess]
  simp only [sub_re,mul_re,re_ofNat,im_ofNat,ofReal_re,ofReal_im,mul_zero,sub_zero]
  nlinarith [sq_nonneg ‖v‖]

theorem convex_positiveQuadrant : Convex ℝ positiveQuadrant := by
  intro a ha b hb u v hu hv _ n
  constructor
  · change (u • a n+v • b n).im=0
    simp [(ha n).1,(hb n).1]
  · change 0 ≤ (u • a n+v • b n).re
    simpa only [add_re,smul_re,smul_eq_mul] using add_nonneg (mul_nonneg hu (ha n).2) (mul_nonneg hv (hb n).2)

theorem strictConcaveOn_action_positive_ball
    (H : ActionSpace → ℂ) (V : Set ActionSpace) (hV : IsOpen V)
    (hH : AnalyticOnNhd ℂ H V) (r : ℝ) (hball : ball (0 : ActionSpace) r ⊆ V)
    (hess : ∀ a ∈ ball (0 : ActionSpace) r, ∀ v : ActionSpace, (∀ n : ℕ+, (v n).im=0) →
      (fderiv ℂ (fderiv ℂ H) a v v).re ≤ -‖v‖^2) :
    StrictConcaveOn ℝ (ball (0 : ActionSpace) r ∩ positiveQuadrant) (fun a => (H a).re) := by
  apply Coeff.strictConcaveOn_re_of_hessian_neg H V _ hV hH
    ((convex_ball (0 : ActionSpace) r).inter convex_positiveQuadrant) (fun _ ha => hball ha.1)
  intro x hx y hy hxy z hz
  have hb := hess z hz.1 (y-x) (by
    intro n
    change (y n-x n).im=0
    simp only [sub_im,(hx.2 n).1,(hy.2 n).1,sub_self])
  exact hb.trans_lt (neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy.symm))))

end NLS.Articles.KdVConvexity
