import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import NLS.ComplexAnalysis.RealCenteredDiscExterior
import NLS.ComplexAnalysis.InversionCircleCoefficients

/-! # Integrating an exterior quadratic derivative remainder

An analytic inverse-frequency derivative remainder integrates to an
analytic function vanishing at zero, plus a single exterior constant.
-/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis

theorem isPreconnected_complex_norm_exterior (R : ℝ) (hR : 0 < R) :
    IsPreconnected {z : ℂ | R < ‖z‖} := by
  have ha : (R+1:ℂ) ∈ realCenteredDiscExterior (fun _ : Unit => (0:ℂ)) (fun _ => R) := by
    intro _
    simp only [dist_zero_right]
    have hn : ‖(R+1:ℂ)‖ = R+1 := by
      rw [← ofReal_one,← ofReal_add,norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
    rw [hn]
    linarith
  simpa only [realCenteredDiscExterior,dist_zero_right,forall_const] using
    (isPathConnected_realCenteredDiscExterior (fun _ : Unit => (0:ℂ)) (fun _ => R)
      (fun _ => rfl) R (fun _ => le_rfl) (R+1) ha (by simp)).isConnected.isPreconnected

theorem exists_exterior_inversion_remainder (F h : ℂ → ℂ) (R r : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hrR : r⁻¹ < R)
    (hh : AnalyticOnNhd ℂ h (ball 0 r))
    (hF : ∀ z : ℂ, R < ‖z‖ → HasDerivAt F (-I+z⁻¹^2*h z⁻¹) z) :
    ∃ A : ℂ → ℂ, AnalyticOnNhd ℂ A (ball 0 r) ∧ A 0 = 0 ∧
      (∀ w ∈ ball (0:ℂ) r, HasDerivAt A (-h w) w) ∧
      ∃ c : ℂ, ∀ z : ℂ, R < ‖z‖ → F z = -I*z+A z⁻¹+c := by
  obtain ⟨G,hG⟩ := exists_primitive_on_convex h (ball 0 r) (convex_ball _ _) isOpen_ball hh.differentiableOn
  let A : ℂ → ℂ := fun w => -(G w-G 0)
  have hA (w : ℂ) (hw : w ∈ ball (0:ℂ) r) : HasDerivAt A (-h w) w := ((hG w hw).sub_const (G 0)).neg
  have ha : AnalyticOnNhd ℂ A (ball 0 r) :=
    (show DifferentiableOn ℂ A (ball 0 r) from fun w hw => (hA w hw).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  let P : ℂ → ℂ := fun z => -I*z+A z⁻¹
  have hP (z : ℂ) (hz : R < ‖z‖) : HasDerivAt P (-I+z⁻¹^2*h z⁻¹) z := by
    have hzpos := hR.trans hz
    have hz0 := norm_pos_iff.mp hzpos
    have hzin : z⁻¹ ∈ ball (0:ℂ) r := by
      rw [mem_ball,dist_zero_right,norm_inv]
      exact (inv_lt_comm₀ hzpos hr).mpr (hrR.trans hz)
    have hd := ((hasDerivAt_id z).const_mul (-I)).add ((hA z⁻¹ hzin).comp z (hasDerivAt_inv hz0))
    convert! hd using 1
    simp only [mul_one,inv_pow]
    ring
  have hopen : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨c,hc⟩ := hopen.exists_eq_add_of_deriv_eq (isPreconnected_complex_norm_exterior R hR)
    (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hP z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hF z hz).deriv.trans (hP z hz).deriv.symm)
  exact ⟨A,ha,by simp [A],hA,c,fun z hz => hc hz⟩

/-- A holomorphic remainder vanishing at zero has a convergent scalar
power series starting with the first power, with no constant term. -/
theorem exists_hasSum_positive_powers_with_first (A : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hA : AnalyticOnNhd ℂ A (ball 0 r)) (hA0 : A 0 = 0) :
    ∃ a : ℕ → ℂ, a 0 = deriv A 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, ‖w‖ < ε →
      HasSum (fun k : ℕ => a k*w^(k+1)) (A w) := by
  have hJ := analyticOnNhd_dslope_zero A r hr hA
  obtain ⟨q,hq⟩ := hJ 0 (mem_ball_self hr)
  have hs := hasFPowerSeriesAt_iff.mp hq
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨q.coeff,?_,ε,hε,?_⟩
  · simpa only [FormalMultilinearSeries.coeff,dslope_same] using hq.coeff_zero 1
  intro w hw
  have ht := (hsub (show w ∈ ball (0:ℂ) ε by simpa only [mem_ball,dist_zero_right] using hw)).mul_left w
  have he : w*dslope A 0 w = A w := by
    simpa only [sub_zero,smul_eq_mul,hA0] using sub_smul_dslope A 0 w
  simpa only [zero_add,smul_eq_mul,he,pow_succ,mul_assoc,mul_comm,mul_left_comm] using ht

theorem exists_hasSum_positive_powers (A : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hA : AnalyticOnNhd ℂ A (ball 0 r)) (hA0 : A 0 = 0) :
    ∃ a : ℕ → ℂ, ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, ‖w‖ < ε →
      HasSum (fun k : ℕ => a k*w^(k+1)) (A w) := by
  obtain ⟨a,_,h⟩ := exists_hasSum_positive_powers_with_first A r hr hA hA0
  exact ⟨a,h⟩

/-- The leading inverse-frequency coefficient is recovered by a limit in
all directions at infinity. -/
theorem tendsto_mul_inversion_remainder (A : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hA : AnalyticOnNhd ℂ A (ball 0 r)) (hA0 : A 0 = 0) :
    Tendsto (fun z : ℂ => z*A z⁻¹) (Bornology.cobounded ℂ) (𝓝 (deriv A 0)) := by
  have ht := ((analyticOnNhd_dslope_zero A r hr hA) 0 (mem_ball_self hr)).continuousAt.tendsto.comp
    tendsto_inv₀_cobounded
  simp only [dslope_same] at ht
  apply ht.congr'
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with z hz
  have he : z⁻¹*dslope A 0 z⁻¹ = A z⁻¹ := by
    simpa only [sub_zero,smul_eq_mul,hA0] using sub_smul_dslope A 0 z⁻¹
  dsimp only [Function.comp_def]
  rw [← he,← mul_assoc,mul_inv_cancel₀ (norm_pos_iff.mp hz),one_mul]

end NLS.ComplexAnalysis
