import NLS.ComplexAnalysis.BanachSmoothAnalytic
import NLS.ComplexAnalysis.BanachTaylorBoundsOn

/-!
# Local complex smoothness implies analyticity

The global Banach-space result can be localized: Taylor coefficients are
bounded on a neighborhood, and Cauchy's theorem sums them along short lines.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal NNReal ContDiff
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Taylor series of a one-variable function smooth on a disk sums at one. -/
theorem hasSum_local_taylor_one (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (closedBall 0 2)) :
    HasSum (fun n : ℕ => iteratedDeriv n f 0/(n.factorial : ℂ)) (f 1) := by
  have hp := hf.hasFPowerSeriesOnBall (by norm_num : (0 : ℝ≥0) < 2)
  have ha : AnalyticAt ℂ f 0 := hf.analyticAt (by
    exact closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 2))
  have he := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries ha.hasFPowerSeriesAt
  rw [he] at hp
  have hs := hp.hasSum (y := 1) (by simp)
  simpa only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.coeff_ofScalars, Finset.prod_const_one, smul_eq_mul,
    one_mul, zero_add] using hs

/-- On an open set, affine-line jets are diagonal evaluations of the Fréchet jets. -/
theorem iteratedDeriv_affineLine_eq_on (f : E → ℂ) {S : Set E}
    (hS : IsOpen S) (hf : ContDiffOn ℂ ∞ f S) {c : E} (hc : c ∈ S)
    (y : E) (n : ℕ) :
    iteratedDeriv n (fun a : ℂ => f (c+a • y)) 0 =
      iteratedFDeriv ℂ n f c (fun _ : Fin n => y) := by
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight y
  let T : Set E := (fun z : E => c+z) ⁻¹' S
  have hT : IsOpen T := hS.preimage (continuous_const.add continuous_id)
  have hTc : (0 : E) ∈ T := by simpa [T] using hc
  have hk : ContDiffOn ℂ ∞ (fun z : E => f (c+z)) T :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hz => hz)
  have hLT : IsOpen (L ⁻¹' T) := hT.preimage L.continuous
  have hL0 : (0 : ℂ) ∈ L ⁻¹' T := by simpa [L] using hTc
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℂ n ((fun z : E => f (c+z)) ∘ L) 0 (fun _ => 1) = _
  rw [← (iteratedFDerivWithin_of_isOpen n hLT hL0),
    L.iteratedFDerivWithin_comp_right hk hT.uniqueDiffOn hLT.uniqueDiffOn
      (by simpa [L] using hTc) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)),
    map_zero, (iteratedFDerivWithin_of_isOpen n hT hTc)]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, L,
    iteratedFDeriv_comp_add_left]

/-- Short affine lines stay in the smoothness domain, so the Fréchet Taylor series sums there. -/
theorem hasSum_complexTaylorSeries_on (f : E → ℂ) {S : Set E}
    (hS : IsOpen S) (hf : ContDiffOn ℂ ∞ f S) {c : E}
    (hc : c ∈ S) (R : ℝ) (hR : 0 < R) (hball : ball c R ⊆ S)
    {y : E} (hy : ‖y‖ < R/3) :
    HasSum (fun n : ℕ => complexTaylorSeries f c n (fun _ : Fin n => y)) (f (c+y)) := by
  have hline : DifferentiableOn ℂ (fun a : ℂ => f (c+a • y)) (closedBall 0 2) := by
    intro a ha
    have ha' : ‖a‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right] using ha
    have hcy : c+a • y ∈ S := hball (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
      have ha0 : 0 ≤ ‖a‖ := norm_nonneg _
      nlinarith)
    exact (((hf.contDiffAt (hS.mem_nhds hcy)).differentiableAt (by simp)).comp a
      (by fun_prop)).differentiableWithinAt
  have hs := hasSum_local_taylor_one _ hline
  simpa only [iteratedDeriv_affineLine_eq_on f hS hf hc y,
    complexTaylorSeries, smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm,
    one_smul] using hs

/-- A complex-smooth scalar map on an open Banach-space domain has a local power series. -/
theorem hasFPowerSeriesOnBall_of_complexSmoothOn (f : E → ℂ) {S : Set E}
    (hS : IsOpen S) (hf : ContDiffOn ℂ ∞ f S) {c : E} (hc : c ∈ S) :
    ∃ r : ℝ≥0∞, HasFPowerSeriesOnBall f (complexTaylorSeries f c) c r := by
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hS c hc
  let t : ℝ≥0 := ⟨R/3, by positivity⟩
  have ht : 0 < (t : ℝ≥0∞) := by
    exact_mod_cast (show 0 < R/3 by positivity)
  let p := complexTaylorSeries f c
  let r : ℝ≥0∞ := min (t : ℝ≥0∞) p.radius
  have hr : 0 < r := lt_min ht (complexTaylorSeries_radius_pos_on f hS hf hc)
  refine ⟨r, ⟨min_le_right _ _, hr, ?_⟩⟩
  intro y hy
  have hy' : ‖y‖ < R/3 := by
    have hy0 : ‖y‖ₑ < r := by simpa only [mem_eball, edist_zero_right] using hy
    have he' : ‖y‖ₑ < (t : ℝ≥0∞) := hy0.trans_le (min_le_left _ _)
    have he : ENNReal.ofReal ‖y‖ < (t : ℝ≥0∞) := by simpa only [ofReal_norm] using he'
    have htR : (t : ℝ≥0∞) = ENNReal.ofReal (R/3) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (by positivity : 0 ≤ R/3)]
      rfl
    rw [htR] at he
    exact (ENNReal.ofReal_lt_ofReal_iff (show 0 < R/3 by positivity)).mp he
  exact hasSum_complexTaylorSeries_on f hS hf hc R hR hball hy'

/-- Complex smoothness on an open set implies Banach-space analyticity there. -/
theorem analyticOnNhd_of_complexSmoothOn (f : E → ℂ) {S : Set E}
    (hS : IsOpen S) (hf : ContDiffOn ℂ ∞ f S) : AnalyticOnNhd ℂ f S :=
  fun _c hc => (hasFPowerSeriesOnBall_of_complexSmoothOn f hS hf hc).choose_spec.analyticAt

end NLS.ComplexAnalysis
