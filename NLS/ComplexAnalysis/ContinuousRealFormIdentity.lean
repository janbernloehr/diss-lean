import NLS.ComplexAnalysis.RealFormIdentity
import Mathlib.Analysis.Normed.Module.Connected

/-! # The real-form identity principle without projection norm restrictions

Continuous real and imaginary parts at zero suffice for local uniqueness.
The global theorem uses connectedness, without assuming convexity.
-/

noncomputable section
open Set Metric Filter Complex
open scoped Topology
namespace NLS.ComplexAnalysis

/-- Local uniqueness from any continuous real-form decomposition, without norm bounds. -/
theorem DifferentiableOn.eventually_eq_zero_of_continuous_real_form
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (R : Set E) (φ : E) (hφR : φ ∈ R)
    (hRadd : ∀ ⦃x y : E⦄, x ∈ R → y ∈ R → x + y ∈ R)
    (hRsmul : ∀ (t : ℝ) ⦃x : E⦄, x ∈ R → (t : ℂ) • x ∈ R)
    (A B : E → E)
    (hAR : ∀ v, A v ∈ R) (hBR : ∀ v, B v ∈ R)
    (hdecomp : ∀ v, v = A v + Complex.I • B v)
    (hA : ContinuousAt A 0) (hA0 : A 0 = 0)
    (hB : ContinuousAt B 0) (hB0 : B 0 = 0)
    (V : Set E) (hVopen : IsOpen V) (hφV : φ ∈ V)
    (f : E → F) (hFdiff : DifferentiableOn ℂ f V)
    (hFzero : ∀ x ∈ V, x ∈ R → f x = 0) :
    ∀ᶠ ψ in 𝓝 φ, f ψ = 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hφV)
  have hv : Tendsto (fun ψ : E => ψ-φ) (𝓝 φ) (𝓝 0) := by
    simpa only [id_eq,sub_self] using ((tendsto_id : Tendsto (fun ψ : E => ψ) (𝓝 φ) (𝓝 φ)).sub_const φ)
  have hAv : Tendsto (fun ψ : E => A (ψ-φ)) (𝓝 φ) (𝓝 0) := by
    simpa only [hA0,Function.comp_def] using hA.tendsto.comp hv
  have hBv : Tendsto (fun ψ : E => B (ψ-φ)) (𝓝 φ) (𝓝 0) := by
    simpa only [hB0,Function.comp_def] using hB.tendsto.comp hv
  filter_upwards [hAv.eventually (ball_mem_nhds 0 (by positivity : 0 < ε/4)),
    hBv.eventually (ball_mem_nhds 0 (by positivity : 0 < ε/4))] with ψ hψA hψB
  let v : E := ψ - φ
  let a : E := A v
  let b : E := B v
  let line : ℂ → E := fun z => φ + a + z • b
  let g : ℂ → F := fun z => f (line z)
  have ha : ‖a‖ < ε/4 := by simpa only [mem_ball,dist_zero_right] using hψA
  have hb : ‖b‖ < ε/4 := by simpa only [mem_ball,dist_zero_right] using hψB
  have hlineV (z : ℂ) (hz : z ∈ ball (0:ℂ) 2) : line z ∈ V := by
    apply hball
    change dist (φ + a + z • b) φ < ε
    rw [dist_eq_norm, show φ + a + z • b - φ = a + z • b by abel]
    have hz2 : ‖z‖ < 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    calc
      ‖a + z • b‖ ≤ ‖a‖ + ‖z • b‖ := norm_add_le _ _
      _ = ‖a‖ + ‖z‖ * ‖b‖ := by rw [norm_smul]
      _ ≤ ‖a‖ + 2 * ‖b‖ := by gcongr
      _ < ε := by linarith
  have hlineDiff : Differentiable ℂ line := by
    dsimp [line]
    fun_prop
  have hgDiff : DifferentiableOn ℂ g (ball (0:ℂ) 2) := by
    intro z hz
    exact (((hFdiff (line z) (hlineV z hz)).differentiableAt
      (hVopen.mem_nhds (hlineV z hz))).comp z (hlineDiff z)).differentiableWithinAt
  have hgAnalytic : AnalyticOnNhd ℂ g (ball (0:ℂ) 2) :=
    hgDiff.analyticOnNhd isOpen_ball
  have hgReal : ∃ η : ℝ, 0 < η ∧
      ∀ t : ℝ, |t| < η → g (t:ℂ) = 0 := by
    refine ⟨1, by norm_num, ?_⟩
    intro t ht
    have htball : (t:ℂ) ∈ ball (0:ℂ) 2 := by
      change dist (t:ℂ) 0 < 2
      simpa [dist_eq_norm, Complex.norm_real] using (lt_trans ht (by norm_num : (1:ℝ) < 2))
    apply hFzero (line (t:ℂ)) (hlineV (t:ℂ) htball)
    exact hRadd (hRadd hφR (hAR v)) (hRsmul t (hBR v))
  have hgEvent : ∀ᶠ z in 𝓝 (0:ℂ), g z = 0 :=
    AnalyticAt.eventually_eq_zero_of_real_interval
      (hgAnalytic 0 (by simp)) hgReal
  have hgZero : EqOn g 0 (ball (0:ℂ) 2) :=
    hgAnalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      Metric.isPreconnected_ball (by simp) hgEvent
  have hIball : Complex.I ∈ ball (0:ℂ) 2 := by
    simp [Metric.mem_ball, dist_eq_norm, Complex.norm_I]
  have hlineI : line Complex.I = ψ := by
    have hvdec : v = a + Complex.I • b := hdecomp v
    calc
      line Complex.I = φ + (a + Complex.I • b) := by dsimp [line]; abel
      _ = φ + v := by rw [← hvdec]
      _ = ψ := by dsimp [v]; abel
  simpa only [Pi.zero_apply, g, hlineI] using hgZero hIball

/-- Vanishing on a nonempty real slice determines the function on a connected open domain. -/
theorem AnalyticOnNhd.eqOn_zero_of_continuous_real_form
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (R : Set E)
    (hRadd : ∀ ⦃x y : E⦄, x ∈ R → y ∈ R → x + y ∈ R)
    (hRsmul : ∀ (t : ℝ) ⦃x : E⦄, x ∈ R → (t : ℂ) • x ∈ R)
    (A B : E → E)
    (hAR : ∀ v, A v ∈ R) (hBR : ∀ v, B v ∈ R)
    (hdecomp : ∀ v, v = A v + Complex.I • B v)
    (hA : ContinuousAt A 0) (hA0 : A 0 = 0)
    (hB : ContinuousAt B 0) (hB0 : B 0 = 0)
    (U : Set E) (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hreal : (U ∩ R).Nonempty) (f : E → F) (hf : AnalyticOnNhd ℂ f U)
    (hzero : ∀ x ∈ U, x ∈ R → f x = 0) : EqOn f 0 U := by
  obtain ⟨φ,hφU,hφR⟩ := hreal
  have hgerm := DifferentiableOn.eventually_eq_zero_of_continuous_real_form
    R φ hφR hRadd hRsmul A B hAR hBR hdecomp hA hA0 hB hB0
    U hUopen hφU f hf.differentiableOn hzero
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn hφU hgerm

end NLS.ComplexAnalysis
