import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # Recovering a quadratic exterior coefficient from a normalized primitive

An analytic remainder has a normalized local primitive. Composing it with
inversion produces an exterior primitive with an explicit first ray
coefficient. Two exterior primitives with finite normalized coefficients
have the same coefficient, since their constant difference on the upper
ray must vanish.
-/
noncomputable section
open Set Complex Filter Topology Metric
namespace NLS.ComplexAnalysis

/-- A finite coefficient at scale `2y` forces the unscaled remainder to vanish. -/
theorem tendsto_zero_of_twice_height_scaled_limit (u : ℝ → ℂ) (M : ℂ)
    (h : Tendsto (fun y : ℝ => (2*y : ℂ)*u y) atTop (𝓝 M)) :
    Tendsto u atTop (𝓝 0) := by
  have hiR := (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).inv_tendsto_atTop
  have hi : Tendsto (fun y : ℝ => (2*y : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Pi.inv_apply, id_eq, ofReal_inv,
      ofReal_mul, ofReal_ofNat, ofReal_zero] using
      continuous_ofReal.continuousAt.tendsto.comp hiR
  have hh := h.mul hi
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  field_simp [ofReal_ne_zero.mpr (ne_of_gt hy)]

/-- The finite upper-ray coefficient is independent of the exterior
primitive once its linear part is normalized to `-iz`. -/
theorem exterior_primitive_coefficient_unique (F G q : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hF : ∀ z : ℂ, R < ‖z‖ → HasDerivAt F (q z) z)
    (hG : ∀ z : ℂ, R < ‖z‖ → HasDerivAt G (q z) z)
    (M N : ℂ)
    (hM : Tendsto (fun y : ℝ => (2*y : ℂ)*(F ((y : ℂ)*I)-y)) atTop (𝓝 M))
    (hN : Tendsto (fun y : ℝ => (2*y : ℂ)*(G ((y : ℂ)*I)-y)) atTop (𝓝 N)) : M = N := by
  have hn (y : ℝ) (hy : y ∈ Ioi R) : R < ‖(y : ℂ)*I‖ := by
    simpa only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_pos (hR.trans hy), mem_Ioi] using hy
  have hf (y : ℝ) (hy : y ∈ Ioi R) :
      HasDerivAt (fun y : ℝ => F ((y : ℂ)*I)) (q ((y : ℂ)*I)*I) y := by
    simpa only [one_mul, Function.comp_def] using!
      ((hF _ (hn y hy)).comp (y : ℂ) ((hasDerivAt_id (y : ℂ)).mul_const I)).comp_ofReal
  have hg (y : ℝ) (hy : y ∈ Ioi R) :
      HasDerivAt (fun y : ℝ => G ((y : ℂ)*I)) (q ((y : ℂ)*I)*I) y := by
    simpa only [one_mul, Function.comp_def] using!
      ((hG _ (hn y hy)).comp (y : ℂ) ((hasDerivAt_id (y : ℂ)).mul_const I)).comp_ofReal
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_eq_add_of_deriv_eq (convex_Ioi R).isPreconnected
    (fun y hy => (hf y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hg y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hf y hy).deriv.trans (hg y hy).deriv.symm)
  have hF0 := tendsto_zero_of_twice_height_scaled_limit _ M hM
  have hG0 := tendsto_zero_of_twice_height_scaled_limit _ N hN
  have hdiff : Tendsto (fun y : ℝ => F ((y : ℂ)*I)-G ((y : ℂ)*I)) atTop (𝓝 0) := by
    simpa only [sub_sub_sub_cancel_right, sub_zero] using hF0.sub hG0
  have hc0 : c = 0 := by
    have ht : Tendsto (fun _ : ℝ => c) atTop (𝓝 0) := by
      apply hdiff.congr'
      filter_upwards [eventually_gt_atTop R] with y hy
      have he : F ((y : ℂ)*I) = G ((y : ℂ)*I) + c := hc hy
      rw [he, add_sub_cancel_left]
    exact tendsto_nhds_unique tendsto_const_nhds ht
  have hM' : Tendsto (fun y : ℝ => (2*y : ℂ)*(G ((y : ℂ)*I)-y)) atTop (𝓝 M) := by
    apply hM.congr'
    filter_upwards [eventually_gt_atTop R] with y hy
    have he : F ((y : ℂ)*I) = G ((y : ℂ)*I) + c := hc hy
    rw [he, hc0, add_zero]
  exact tendsto_nhds_unique hM' hN

/-- An analytic quadratic remainder produces an exterior primitive whose
upper-ray coefficient is exactly `2i` times the remainder's value at zero. -/
theorem exists_exterior_primitive_of_quadratic_remainder
    (h : ℂ → ℂ) (r : ℝ) (hr : 0 < r) (hh : AnalyticOnNhd ℂ h (ball 0 r)) :
    ∃ P : ℂ → ℂ,
      (∀ z : ℂ, r⁻¹ < ‖z‖ → HasDerivAt P (-I + z⁻¹^2*h z⁻¹) z) ∧
      Tendsto (fun y : ℝ => (2*y : ℂ)*(P ((y : ℂ)*I)-y)) atTop (𝓝 (2*I*h 0)) := by
  obtain ⟨G, hG⟩ := exists_primitive_on_convex h (ball 0 r) (convex_ball _ _) isOpen_ball hh.differentiableOn
  let H := fun w => G w - G 0
  have hH (w : ℂ) (hw : w ∈ ball (0 : ℂ) r) : HasDerivAt H (h w) w := (hG w hw).sub_const (G 0)
  have hH0 : H 0 = 0 := sub_self _
  let P := fun z : ℂ => -I*z - H z⁻¹
  refine ⟨P, ?_, ?_⟩
  · intro z hz
    have hzpos : 0 < ‖z‖ := (inv_pos.mpr hr).trans hz
    have hz0 := norm_pos_iff.mp hzpos
    have hzin : z⁻¹ ∈ ball (0 : ℂ) r := by
      rw [mem_ball, dist_zero_right, norm_inv]
      exact (inv_lt_comm₀ hzpos hr).mpr hz
    have hd := ((hasDerivAt_id z).const_mul (-I)).sub
      ((hH z⁻¹ hzin).comp z (hasDerivAt_inv hz0))
    convert! hd using 1
    simp only [mul_one, inv_pow]
    ring
  · have hiR : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
    have hi : Tendsto (fun y : ℝ => (y : ℂ)⁻¹) atTop (𝓝 (0 : ℂ)) := by
      simpa only [Function.comp_def, ofReal_inv, ofReal_zero] using
        continuous_ofReal.continuousAt.tendsto.comp hiR
    have hw : Tendsto (fun y : ℝ => ((y : ℂ)*I)⁻¹) atTop (𝓝 (0 : ℂ)) := by
      simpa only [mul_inv_rev, mul_zero] using hi.const_mul I⁻¹
    have hderiv := hH 0 (mem_ball_self hr)
    have hs : Tendsto (fun y : ℝ => dslope H 0 ((y : ℂ)*I)⁻¹) atTop (𝓝 (h 0)) := by
      simpa only [dslope_same, hderiv.deriv, Function.comp_def] using
        (continuousAt_dslope_same.mpr hderiv.differentiableAt).tendsto.comp hw
    have ht := hs.const_mul (2*I)
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
    have he := sub_smul_dslope H 0 ((y : ℂ)*I)⁻¹
    simp only [sub_zero, smul_eq_mul, hH0] at he
    dsimp only [P]
    rw [← he]
    field_simp
    ring_nf
    norm_num [pow_succ, I_sq]

end NLS.ComplexAnalysis
