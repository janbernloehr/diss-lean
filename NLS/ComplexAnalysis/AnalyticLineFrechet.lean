import NLS.ComplexAnalysis.AnalyticLineRemainder
import NLS.ComplexAnalysis.BanachHolomorphicC1

/-! # From analytic lines to Fréchet differentiability

A continuous map on an open complex normed domain with analytic line
restrictions has a complex Fréchet derivative. A local quadratic error
bound identifies it with the bounded directional derivative constructed
above. The existing holomorphic regularity theorem also gives `C¹`.
-/
noncomputable section
open Set Metric Filter Topology Asymptotics
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Continuous maps analytic on every complex line are Fréchet differentiable. -/
theorem hasFDerivAt_of_analyticLines
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U)) (a : E) (ha : a ∈ U) :
    HasFDerivAt f (lineDerivativeCLM f U hU hf hl a ha) a := by
  obtain ⟨R₀,hR₀,hUball⟩ := Metric.isOpen_iff.mp hU a ha
  have hfc : ContinuousAt f a := (hf a ha).continuousAt (hU.mem_nhds ha)
  obtain ⟨R₁,hR₁,hFball⟩ := Metric.mem_nhds_iff.mp
    (hfc (ball_mem_nhds (f a) (by norm_num : (0 : ℝ) < 1)))
  let R : ℝ := min R₀ R₁
  have hR : 0 < R := lt_min hR₀ hR₁
  have hball : ball a R ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hUball
  let M : ℝ := ‖f a‖+1
  have hb : ∀ z ∈ ball a R, ‖f z‖ ≤ M := by
    intro z hz
    have hzF : ‖f z-f a‖ < 1 := by
      have hzB : z ∈ ball a R₁ := (ball_subset_ball (min_le_right _ _)) hz
      simpa only [Set.mem_preimage,mem_ball,dist_eq_norm] using hFball hzB
    have h := norm_le_norm_sub_add (f z) (f a)
    dsimp [M]
    linarith
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have ho : (fun h : E => f (a+h)-f a-lineDerivativeCLM f U hU hf hl a ha h)
      =O[𝓝 0] (fun h => ‖h‖^2) := by
    apply Asymptotics.IsBigO.of_bound (12*M/R^2)
    filter_upwards [ball_mem_nhds (0 : E) (show 0 < R/2 by positivity)] with h hh
    have hh' : ‖h‖ < R/2 := by simpa only [mem_ball,dist_zero_right] using hh
    simpa only [lineDerivativeCLM_apply,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using
      norm_sub_lineDeriv_le_of_ball_bound f U hU hl a R M hR hball hb h hh'
  exact ho.trans_isLittleO (isLittleO_norm_pow_id (by norm_num : 1 < (2 : ℕ)))

/-- The constructed line derivative agrees with the canonical Fréchet derivative. -/
theorem fderiv_apply_eq_lineDeriv_of_analyticLines
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U)) (a : E) (ha : a ∈ U) (v : E) :
    fderiv ℂ f a v = lineDeriv ℂ f a v := by
  rw [(hasFDerivAt_of_analyticLines f U hU hf hl a ha).fderiv]
  rfl

/-- Fréchet differentiability holds throughout the open line-analytic domain. -/
theorem differentiableOn_of_analyticLines
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U)) : DifferentiableOn ℂ f U := by
  intro a ha
  exact (hasFDerivAt_of_analyticLines f U hU hf hl a ha).differentiableAt.differentiableWithinAt

/-- The resulting derivative is continuous in operator norm. -/
theorem contDiffOn_one_of_analyticLines
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U)) : ContDiffOn ℂ 1 f U :=
  contDiffOn_one_of_differentiableOn f hU (differentiableOn_of_analyticLines f U hU hf hl)

end NLS.ComplexAnalysis
