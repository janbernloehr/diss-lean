import NLS.ComplexAnalysis.FDerivCauchyFormula
import NLS.ComplexAnalysis.AnalyticLineFrechet

/-! # Analytic line restrictions of the Fréchet derivative

The operator-valued Cauchy formula gives a power series for every affine
line restriction of the derivative. Together with norm continuity, the
line-to-Fréchet theorem shows that the derivative is itself holomorphic.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped NNReal
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Each line restriction of the derivative has an operator-norm power series at zero. -/
theorem analyticAt_fderiv_affineLine_zero
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (a : E) (ha : a ∈ U) (v : E) :
    AnalyticAt ℂ (fun z : ℂ => fderiv ℂ f (a+z • v)) 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU a ha
  let R : ℝ≥0 := ⟨ε/(4*(‖v‖+1)),by positivity⟩
  have hR : 0 < R := by
    change (0 : ℝ) < ε/(4*(‖v‖+1))
    positivity
  have hRmul : (R : ℝ)*(‖v‖+1) = ε/4 := by
    change (ε/(4*(‖v‖+1)))*(‖v‖+1) = ε/4
    field_simp
  let V : Set E := ball a (ε/2)
  have hV : IsOpen V := isOpen_ball
  have haV : a ∈ V := mem_ball_self (by positivity)
  have hinto (b : E) (hb : b ∈ V) (z : ℂ) (hz : z ∈ closedBall 0 R) : b+z • v ∈ U := by
    apply hball
    have hb' : ‖b-a‖ < ε/2 := by simpa only [V,mem_ball,dist_eq_norm] using hb
    have hz' : ‖z‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hprod : ‖z‖*‖v‖ ≤ ε/4 := by
      calc
        ‖z‖*‖v‖ ≤ (R : ℝ)*(‖v‖+1) := mul_le_mul hz' (by linarith) (norm_nonneg _) R.coe_nonneg
        _ = ε/4 := hRmul
    rw [mem_ball,dist_eq_norm]
    calc
      ‖b+z • v-a‖ = ‖(b-a)+z • v‖ := by congr 1; abel
      _ ≤ ‖b-a‖+‖z‖*‖v‖ := by simpa only [norm_smul] using norm_add_le (b-a) (z • v)
      _ < ε := by linarith
  have hdf : ContinuousOn (fderiv ℂ f) U :=
    (contDiffOn_one_of_differentiableOn f hU hf).continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hc : ContinuousOn (fun z : ℂ => fderiv ℂ f (a+z • v)) (sphere 0 R) :=
    hdf.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (fun z hz => hinto a haV z (sphere_subset_closedBall hz))
  have hp := hasFPowerSeriesOn_cauchy_integral (hc.circleIntegrable R.coe_nonneg) hR
  apply hp.analyticAt.congr
  filter_upwards [ball_mem_nhds (0 : ℂ) (show 0 < (R : ℝ) from hR)] with w hw
  rw [circleIntegral_fderiv_affineLine f U hU hf a v R hR V hV haV hinto w hw,
    inv_smul_smul₀]
  simp [Real.pi_ne_zero,Complex.I_ne_zero]

/-- The derivative is analytic along every line on the line's full domain. -/
theorem analyticOnNhd_fderiv_affineLine
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (a v : E) :
    AnalyticOnNhd ℂ (fun z : ℂ => fderiv ℂ f (a+z • v))
      ((fun z : ℂ => a+z • v) ⁻¹' U) := by
  intro t ht
  have hh : AnalyticAt ℂ (fun u : ℂ => fderiv ℂ f (a+t • v+u • v)) (t-t) := by
    simpa only [sub_self] using analyticAt_fderiv_affineLine_zero f U hU hf (a+t • v) ht v
  have hshift : AnalyticAt ℂ (fun u : ℂ => u-t) t := analyticAt_id.sub analyticAt_const
  have he (u : ℂ) : a+t • v+(u-t) • v = a+u • v := by rw [sub_smul]; abel
  simpa only [Function.comp_def,he] using hh.comp (f := fun u : ℂ => u-t) hshift

/-- Complex Fréchet differentiability on an open set is preserved by differentiation. -/
theorem differentiableOn_fderiv_of_differentiableOn
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fderiv ℂ f) U :=
  differentiableOn_of_analyticLines _ _ hU
    ((contDiffOn_one_of_differentiableOn f hU hf).continuousOn_fderiv_of_isOpen hU (by norm_num))
    (fun a _ v => analyticOnNhd_fderiv_affineLine f U hU hf a v)

end NLS.ComplexAnalysis
