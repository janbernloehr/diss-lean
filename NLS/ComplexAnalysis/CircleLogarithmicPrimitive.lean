import NLS.ComplexAnalysis.CircleCauchyTransform
import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# A single-valued primitive of an exterior zero-period Cauchy transform

The normalized logarithm `log (1 - (w-c)/(z-c))` stays in its analytic
slit when `w` is on the density circle and `z` is outside its closed
disc. Its derivative differs from the Cauchy kernel by a constant in
`w`. A zero density period cancels that term, producing a primitive
on the whole exterior, with no restriction on a path's winding.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

def circleLogarithmicPrimitive (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  (2*Real.pi*I : ℂ)⁻¹ * ∮ w in C(c,r), f w*log (1-(w-c)/(z-c))

theorem circleLogKernel_mem_slitPlane (c w z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hw : w ∈ sphere c r) (hz : z ∉ closedBall c r) :
    1-(w-c)/(z-c) ∈ slitPlane := by
  have hzn : r < ‖z-c‖ := by simpa only [mem_closedBall,not_le,dist_eq_norm] using hz
  have hwc : ‖w-c‖ = r := by simpa only [mem_sphere,dist_eq_norm] using hw
  have hnorm : ‖-(w-c)/(z-c)‖ < 1 := by
    rw [norm_div,norm_neg,hwc]
    exact (div_lt_one (lt_of_le_of_lt hr hzn)).mpr hzn
  simpa only [sub_eq_add_neg,neg_div] using mem_slitPlane_of_norm_lt_one hnorm

theorem hasDerivAt_circleLogKernel (c w z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hw : w ∈ sphere c r) (hz : z ∉ closedBall c r) :
    HasDerivAt (fun v : ℂ => log (1-(w-c)/(v-c)))
      ((z-w)⁻¹-(z-c)⁻¹) z := by
  have hzc : z-c ≠ 0 := by
    have hzn : r < ‖z-c‖ := by simpa only [mem_closedBall,not_le,dist_eq_norm] using hz
    exact norm_pos_iff.mp (lt_of_le_of_lt hr hzn)
  have hzw : z-w ≠ 0 := sub_ne_zero.mpr (fun h => hz (h ▸ sphere_subset_closedBall hw))
  have hslit := circleLogKernel_mem_slitPlane c w z r hr hw hz
  have harg := (hasDerivAt_const z (1:ℂ)).sub
    ((hasDerivAt_const z (w-c)).div ((hasDerivAt_id z).sub_const c) hzc)
  have hargne := slitPlane_ne_zero hslit
  convert (hasDerivAt_log hslit).comp z harg using 1 <;> try rfl
  simp only [id_eq,mul_one,zero_mul,zero_sub,neg_div,neg_neg]
  field_simp [hargne,hzc,hzw]
  ring

/-- Joint analyticity and the derivatives of the spectral slices give the
derivative of a scalar fixed-circle integral. -/
theorem hasDerivAt_circleIntegral_parameter
    (F : ℂ × ℂ → ℂ) (D : Set (ℂ × ℂ)) (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (V : Set ℂ) (hV : IsOpen V)
    (hcircle : ∀ z ∈ V, ∀ w ∈ sphere c r, (w,z) ∈ D)
    (z : ℂ) (hz : z ∈ V) (g : ℂ → ℂ)
    (hg : ∀ w ∈ sphere c r, HasDerivAt (fun v : ℂ => F (w,v)) (g w) z) :
    HasDerivAt (fun v : ℂ => ∮ w in C(c,r), F (w,v)) (∮ w in C(c,r), g w) z := by
  let G : ℂ → ℂ →L[ℂ] ℂ := fun w =>
    (fderiv ℂ F (w,z)).comp (ContinuousLinearMap.inr ℂ ℂ ℂ)
  have hGc : ContinuousOn G (sphere c r) :=
    (analyticOnNhd_parameterDerivative F hF).continuousOn.comp
      (continuousOn_id.prodMk continuousOn_const) (fun w hw => hcircle z hz w hw)
  have hd := (hasFDerivAt_circleIntegral_parameterDerivative F hD hF c r hr hV hcircle z hz).hasDerivAt
  change HasDerivAt (fun v : ℂ => ∮ w in C(c,r), F (w,v)) ((∮ w in C(c,r), G w) 1) z at hd
  rw [NLS.CircleIntegral.apply (hGc.circleIntegrable hr) 1] at hd
  convert hd using 1
  apply circleIntegral.integral_congr hr
  intro w hw
  dsimp only [G]
  rw [← fderiv_source_section_eq_joint F w z ((hF (w,z) (hcircle z hz w hw)).differentiableAt)]
  simpa only [deriv] using (hg w hw).deriv.symm

theorem hasDerivAt_circleLogarithmicPrimitive
    (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f (sphere c r))
    (hperiod : (∮ w in C(c,r), f w) = 0)
    (z : ℂ) (hz : z ∉ closedBall c r) :
    HasDerivAt (circleLogarithmicPrimitive f c r) (-circleCauchyTransform f c r z) z := by
  let V : Set ℂ := (closedBall c r)ᶜ
  let D : Set (ℂ × ℂ) := {t | AnalyticAt ℂ f t.1 ∧ t.2 ≠ c ∧
    1-(t.1-c)/(t.2-c) ∈ slitPlane}
  let F : ℂ × ℂ → ℂ := fun t => f t.1*log (1-(t.1-c)/(t.2-c))
  have hD : IsOpen D := by
    have hne : IsOpen {t : ℂ × ℂ | t.2 ≠ c} := isOpen_ne_fun continuous_snd continuous_const
    have hcont : ContinuousOn (fun t : ℂ × ℂ => 1-(t.1-c)/(t.2-c)) {t | t.2 ≠ c} :=
      continuousOn_const.sub ((continuousOn_fst.sub continuousOn_const).div
        (continuousOn_snd.sub continuousOn_const) (fun t ht => sub_ne_zero.mpr ht))
    exact ((isOpen_analyticAt ℂ f).preimage continuous_fst).inter
      (hcont.isOpen_inter_preimage hne isOpen_slitPlane)
  have hF : AnalyticOnNhd ℂ F D := by
    intro t ht
    have harg : AnalyticAt ℂ (fun v : ℂ × ℂ => 1-(v.1-c)/(v.2-c)) t :=
      analyticAt_const.sub ((analyticAt_fst.sub analyticAt_const).div
        (analyticAt_snd.sub analyticAt_const) (sub_ne_zero.mpr ht.2.1))
    exact (ht.1.comp analyticAt_fst).mul
      ((analyticAt_clog ht.2.2).comp (f := fun v : ℂ × ℂ => 1-(v.1-c)/(v.2-c)) harg)
  have hcircle : ∀ v ∈ V, ∀ w ∈ sphere c r, (w,v) ∈ D := by
    intro v hv w hw
    have hvn : r < ‖v-c‖ := by simpa only [V,mem_compl_iff,mem_closedBall,not_le,dist_eq_norm] using hv
    exact ⟨hf w hw,sub_ne_zero.mp (norm_pos_iff.mp (lt_of_le_of_lt hr hvn)),
      circleLogKernel_mem_slitPlane c w v r hr hw hv⟩
  have hd := hasDerivAt_circleIntegral_parameter F D hD hF c r hr V
    isClosed_closedBall.isOpen_compl hcircle z hz
    (fun w => f w*((z-w)⁻¹-(z-c)⁻¹))
    (fun w hw => (hasDerivAt_circleLogKernel c w z r hr hw hz).const_mul (f w))
  have hk : ContinuousOn (fun w : ℂ => f w*(z-w)⁻¹) (sphere c r) :=
    hf.continuousOn.mul ((continuousOn_const.sub continuousOn_id).inv₀
      (fun w hw => sub_ne_zero.mpr (fun he => by
        change z = w at he
        exact hz (he ▸ sphere_subset_closedBall hw))))
  have hconst : CircleIntegrable (fun w => f w*(z-c)⁻¹) c r :=
    (hf.continuousOn.mul continuousOn_const).circleIntegrable hr
  have heq : (∮ w in C(c,r), f w*((z-w)⁻¹-(z-c)⁻¹)) =
      -(∮ w in C(c,r), f w/(w-z)) := by
    have hpc : (∮ w in C(c,r), f w*(z-c)⁻¹) =
        (∮ w in C(c,r), f w)*(z-c)⁻¹ := by
      simpa only [smul_eq_mul] using circleIntegral.integral_smul_const f (z-c)⁻¹ c r
    simp_rw [mul_sub]
    rw [circleIntegral.integral_sub (hk.circleIntegrable hr) hconst,
      hpc,hperiod,zero_mul,sub_zero]
    rw [show -(∮ w in C(c,r), f w/(w-z)) =
      ∮ w in C(c,r), (-1:ℂ)*(f w/(w-z)) by
        rw [circleIntegral.integral_const_mul,neg_one_mul]]
    apply circleIntegral.integral_congr hr
    intro w _
    dsimp only
    rw [show z-w = -(w-z) by ring,inv_neg,mul_neg,div_eq_mul_inv]
    ring
  unfold circleLogarithmicPrimitive circleCauchyTransform
  simpa only [heq,mul_neg] using hd.const_mul (2*Real.pi*I : ℂ)⁻¹

end NLS.ComplexAnalysis
