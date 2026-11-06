import NLS.ComplexAnalysis.NormalAnalyticSeries
import NLS.ComplexAnalysis.BanachHolomorphicLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A normally convergent analytic series has convergent full source
Fréchet derivatives of its actual finite partial sums. -/
theorem tendsto_fderiv_sum_range_of_summable_uniform_bound
    (f : ℕ → E → ℂ) (U : Set E) (hU : IsOpen U)
    (hf : ∀ n : ℕ, AnalyticOnNhd ℂ (f n) U)
    (M : ℕ → ℝ) (hM : Summable M)
    (hb : ∀ n : ℕ, ∀ x∈U, ‖f n x‖≤M n) (a : E) (ha : a∈U) :
    Tendsto (fun N => fderiv ℂ (fun x : E => ∑ n∈Finset.range N,f n x) a)
      atTop (𝓝 (fderiv ℂ (fun x : E => ∑' n : ℕ,f n x) a)) := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let r := ε/2
  have hr : 0<r := half_pos hε
  have hsub : ball a (2*r)⊆U := by
    have he : 2*r=ε := by dsimp only [r];ring
    rw [he]
    exact hball
  have hparts : ∀ N : ℕ, DifferentiableOn ℂ (fun x : E => ∑ n∈Finset.range N,f n x) (ball a (2*r)) := by
    intro N x hx
    have hA : AnalyticAt ℂ (fun y : E => ∑ n∈Finset.range N,f n y) x :=
      Finset.analyticAt_fun_sum _ (fun n _ => hf n x (hsub hx))
    exact hA.differentiableAt.differentiableWithinAt
  have hu := tendstoUniformlyOn_tsum_nat hM hb
  have hd := tendstoUniformlyOn_fderiv_ball (fun N x => ∑ n∈Finset.range N,f n x)
    (fun x => ∑' n : ℕ,f n x) a r hr (Eventually.of_forall hparts) (hu.mono hsub)
  exact hd.2.tendsto_at (mem_ball_self hr)

/-- A proved limit of directional partial-sum derivatives is the
actual derivative of the normally convergent analytic sum. -/
theorem fderiv_tsum_apply_eq_of_partial_sum_limit
    (f : ℕ → E → ℂ) (U : Set E) (hU : IsOpen U)
    (hf : ∀ n : ℕ, AnalyticOnNhd ℂ (f n) U)
    (M : ℕ → ℝ) (hM : Summable M)
    (hb : ∀ n : ℕ, ∀ x∈U, ‖f n x‖≤M n) (a h : E) (ha : a∈U) (L : ℂ)
    (hL : Tendsto (fun N => (fderiv ℂ (fun x : E => ∑ n∈Finset.range N,f n x) a) h) atTop (𝓝 L)) :
    (fderiv ℂ (fun x : E => ∑' n : ℕ,f n x) a) h=L := by
  have hd := tendsto_fderiv_sum_range_of_summable_uniform_bound f U hU hf M hM hb a ha
  have he := (ContinuousLinearMap.apply ℂ ℂ h).continuous.tendsto (fderiv ℂ (fun x : E => ∑' n : ℕ,f n x) a)
  exact tendsto_nhds_unique (he.comp hd) hL

/-- Adding a fixed analytic finite head preserves convergence of the
full source derivatives of the normally convergent partial sums. -/
theorem tendsto_fderiv_add_sum_range_of_summable_uniform_bound
    (A : E → ℂ) (f : ℕ → E → ℂ) (U : Set E) (hU : IsOpen U)
    (hf : ∀ n : ℕ, AnalyticOnNhd ℂ (f n) U)
    (M : ℕ → ℝ) (hM : Summable M)
    (hb : ∀ n : ℕ, ∀ x∈U, ‖f n x‖≤M n) (a : E) (ha : a∈U) (hA : AnalyticAt ℂ A a) :
    Tendsto (fun N => fderiv ℂ (fun x : E => A x+∑ n∈Finset.range N,f n x) a)
      atTop (𝓝 (fderiv ℂ (fun x : E => A x+∑' n : ℕ,f n x) a)) := by
  have hs := (analyticOnNhd_tsum_of_summable_uniform_bound f U hU hf M hM hb) a ha
  have hN (N : ℕ) : AnalyticAt ℂ (fun x : E => ∑ n∈Finset.range N,f n x) a :=
    Finset.analyticAt_fun_sum _ (fun n _ => hf n a ha)
  have hd := tendsto_fderiv_sum_range_of_summable_uniform_bound f U hU hf M hM hb a ha
  rw [fderiv_fun_add hA.differentiableAt hs.differentiableAt]
  apply (tendsto_const_nhds.add hd).congr'
  apply Eventually.of_forall
  intro N
  exact (fderiv_fun_add hA.differentiableAt (hN N).differentiableAt).symm

end NLS.ComplexAnalysis
