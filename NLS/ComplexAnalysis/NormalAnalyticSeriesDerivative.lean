import NLS.ComplexAnalysis.NormalAnalyticSeries
import NLS.ComplexAnalysis.BanachHolomorphicLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Derivatives of normally convergent analytic series -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A common summable bound on an open complex neighborhood justifies the
limit of the partial source derivatives in operator norm. -/
theorem tendsto_fderiv_sum_of_summable_uniform_bound
    (f : ℕ → E → ℂ) (U : Set E) (hU : IsOpen U)
    (hf : ∀ n : ℕ, AnalyticOnNhd ℂ (f n) U)
    (M : ℕ → ℝ) (hM : Summable M)
    (hbound : ∀ n : ℕ, ∀ x ∈ U, ‖f n x‖ ≤ M n)
    (a : E) (ha : a ∈ U) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, fderiv ℂ (f j) a) atTop
      (𝓝 (fderiv ℂ (fun x => ∑' j, f j x) a)) := by
  obtain ⟨s,hs,hsU⟩ := Metric.isOpen_iff.mp hU a ha
  let r := s/2
  have hr : 0<r := by dsimp only [r]; positivity
  have hball : ball a (2*r) ⊆ U := by
    have he : 2*r=s := by dsimp only [r]; ring
    simpa only [he] using hsU
  have hdiff (N : ℕ) : DifferentiableOn ℂ (fun x => ∑ j ∈ Finset.range N, f j x) (ball a (2*r)) := by
    intro x hx
    exact (Finset.analyticAt_fun_sum _ (fun j _ => hf j x (hball hx))).differentiableAt.differentiableWithinAt
  have hconv := tendstoUniformlyOn_tsum_nat hM hbound
  have hd := (tendstoUniformlyOn_fderiv_ball (fun N x => ∑ j ∈ Finset.range N, f j x)
    (fun x => ∑' j, f j x) a r hr (Eventually.of_forall hdiff) (hconv.mono hball)).2
  have he (N : ℕ) : fderiv ℂ (fun x => ∑ j ∈ Finset.range N, f j x) a =
      ∑ j ∈ Finset.range N, fderiv ℂ (f j) a := by
    exact (HasFDerivAt.fun_sum (fun j _ => (hf j a ha).differentiableAt.hasFDerivAt)).fderiv
  simpa only [he] using hd.tendsto_at (mem_ball_self hr)

/-- Evaluation of the operator-norm derivative limit on any fixed source
direction. No separate summability assumption on derivatives is needed. -/
theorem tendsto_fderiv_sum_apply_of_summable_uniform_bound
    (f : ℕ → E → ℂ) (U : Set E) (hU : IsOpen U)
    (hf : ∀ n : ℕ, AnalyticOnNhd ℂ (f n) U)
    (M : ℕ → ℝ) (hM : Summable M)
    (hbound : ∀ n : ℕ, ∀ x ∈ U, ‖f n x‖ ≤ M n)
    (a : E) (ha : a ∈ U) (v : E) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, (fderiv ℂ (f j) a) v) atTop
      (𝓝 ((fderiv ℂ (fun x => ∑' j, f j x) a) v)) := by
  have h := tendsto_fderiv_sum_of_summable_uniform_bound f U hU hf M hM hbound a ha
  have he := ((ContinuousLinearMap.apply ℂ ℂ v).continuous.tendsto _).comp h
  change Tendsto (fun N => (∑ j ∈ Finset.range N, fderiv ℂ (f j) a) v) atTop
    (𝓝 ((fderiv ℂ (fun x => ∑' j, f j x) a) v)) at he
  simpa only [sum_apply] using he

end NLS.ComplexAnalysis
