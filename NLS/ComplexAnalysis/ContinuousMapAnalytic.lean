import NLS.ComplexAnalysis.BanachHolomorphicAnalytic
import NLS.ComplexAnalysis.BilinearCircleIntegral
import Mathlib.Topology.ContinuousMap.Compact

/-! # Analytic maps into spaces of continuous functions

Norm continuity and analytic point evaluations imply analyticity in the
uniform norm. For a complex line this follows by applying evaluation to
Cauchy's integral formula; the Banach-valued line criterion then handles
arbitrary complex normed parameter spaces.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped NNReal
namespace NLS.ComplexAnalysis
variable {K F : Type} [TopologicalSpace K] [CompactSpace K]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Cauchy's formula assembles analytic point evaluations in the uniform norm. -/
theorem analyticOnNhd_continuousMap_of_eval_complex
    (f : ℂ → C(K,F)) {U : Set ℂ} (hU : IsOpen U) (hc : ContinuousOn f U)
    (ha : ∀ k : K, AnalyticOnNhd ℂ (fun z => f z k) U) : AnalyticOnNhd ℂ f U := by
  intro c hcU
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU c hcU
  let R : ℝ≥0 := ⟨r/2,by positivity⟩
  have hR : 0 < R := by change 0 < r/2; positivity
  have hclosed : closedBall c (R : ℝ) ⊆ U :=
    (closedBall_subset_ball (by change r/2 < r; linarith)).trans hball
  have hfc := hc.mono hclosed
  have hp := hasFPowerSeriesOn_cauchy_integral
    ((hfc.mono sphere_subset_closedBall).circleIntegrable R.coe_nonneg) hR
  apply hp.analyticAt.congr
  filter_upwards [ball_mem_nhds c (show 0 < (R : ℝ) from hR)] with w hw
  have hkernel : CircleIntegrable (fun z : ℂ => (z-w)⁻¹ • f z) c R := by
    apply ContinuousOn.circleIntegrable R.coe_nonneg
    have hs : ContinuousOn (fun z : ℂ => (z-w)⁻¹) (sphere c R) := by
      apply (continuousOn_id.sub continuousOn_const).inv₀
      intro z hz he
      have hz' : z = w := sub_eq_zero.mp he
      subst z
      exact (ne_of_lt hw) (mem_sphere.mp hz)
    exact hs.smul (hfc.mono sphere_subset_closedBall)
  apply ContinuousMap.ext
  intro k
  let ev : C(K,F) →L[ℂ] F := ContinuousMap.evalCLM ℂ k
  change ev ((2*(Real.pi : ℂ)*I)⁻¹ • ∮ z in C(c,R), (z-w)⁻¹ • f z) = ev (f w)
  rw [map_smul,map_circleIntegral ev hkernel]
  have hk := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := (∅ : Set ℂ)) countable_empty hw
    (ev.continuous.comp_continuousOn hfc)
    (fun z hz => (ha k z (hclosed (ball_subset_closedBall hz.1))).differentiableAt)
  simpa only [map_smul,Function.comp_def] using! hk

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Point evaluations determine Banach analyticity once uniform-norm continuity is known. -/
theorem analyticOnNhd_continuousMap_of_eval
    (f : E → C(K,F)) {U : Set E} (hU : IsOpen U) (hc : ContinuousOn f U)
    (ha : ∀ k : K, AnalyticOnNhd ℂ (fun z => f z k) U) : AnalyticOnNhd ℂ f U := by
  apply analyticOnNhd_of_analyticLines f U hU hc
  intro a _ v
  have hline : Continuous (fun z : ℂ => a+z • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  apply analyticOnNhd_continuousMap_of_eval_complex _ (hU.preimage hline)
    (hc.comp hline.continuousOn (fun _ h => h))
  intro k z hz
  exact (ha k _ hz).comp (f := fun z : ℂ => a+z • v)
    (analyticAt_const.add (analyticAt_id.smul analyticAt_const))

end NLS.ComplexAnalysis
