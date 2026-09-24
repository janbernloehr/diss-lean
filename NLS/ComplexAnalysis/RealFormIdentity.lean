import NLS.ComplexAnalysis.RealLineIdentity
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Uniqueness from a norm-controlled real form

An analytic scalar function on a complex normed space that vanishes on a
real form near a point vanishes on a complex neighborhood. The real and
imaginary parts of each perturbation are assumed to have norms bounded
by the perturbation's norm. This form is suited to Fourier potentials.
-/

noncomputable section
open Set Metric Filter Complex
open scoped Topology
namespace NLS.ComplexAnalysis

/-- Local uniqueness for complex-differentiable functions along a
norm-controlled real form of a complex normed space. -/
theorem DifferentiableOn.eventually_eq_zero_of_real_form
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : Set E) (φ : E) (hφR : φ ∈ R)
    (hRadd : ∀ ⦃x y : E⦄, x ∈ R → y ∈ R → x + y ∈ R)
    (hRsmul : ∀ (t : ℝ) ⦃x : E⦄, x ∈ R → (t : ℂ) • x ∈ R)
    (A B : E → E)
    (hAR : ∀ v, A v ∈ R) (hBR : ∀ v, B v ∈ R)
    (hdecomp : ∀ v, v = A v + Complex.I • B v)
    (hAnorm : ∀ v, ‖A v‖ ≤ ‖v‖)
    (hBnorm : ∀ v, ‖B v‖ ≤ ‖v‖)
    (V : Set E) (hVopen : IsOpen V) (hφV : φ ∈ V)
    (F : E → ℂ) (hFdiff : DifferentiableOn ℂ F V)
    (hFzero : ∀ x ∈ V, x ∈ R → F x = 0) :
    ∀ᶠ ψ in 𝓝 φ, F ψ = 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hφV)
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ε / 4, by positivity, ?_⟩
  intro ψ hψ
  change F ψ = 0
  let v : E := ψ - φ
  let a : E := A v
  let b : E := B v
  let line : ℂ → E := fun z => φ + a + z • b
  let g : ℂ → ℂ := fun z => F (line z)
  have hv : ‖v‖ < ε / 4 := by
    simpa [v, Metric.mem_ball, dist_eq_norm] using hψ
  have ha : ‖a‖ ≤ ‖v‖ := hAnorm v
  have hb : ‖b‖ ≤ ‖v‖ := hBnorm v
  have hlineV (z : ℂ) (hz : z ∈ ball (0:ℂ) 2) : line z ∈ V := by
    apply hball
    change dist (φ + a + z • b) φ < ε
    rw [dist_eq_norm, show φ + a + z • b - φ = a + z • b by abel]
    have hz2 : ‖z‖ < 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    calc
      ‖a + z • b‖ ≤ ‖a‖ + ‖z • b‖ := norm_add_le _ _
      _ = ‖a‖ + ‖z‖ * ‖b‖ := by rw [norm_smul]
      _ ≤ ‖v‖ + ‖z‖ * ‖v‖ := by
        exact add_le_add ha (mul_le_mul_of_nonneg_left hb (norm_nonneg z))
      _ ≤ ‖v‖ + 2 * ‖v‖ := by gcongr
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

end NLS.ComplexAnalysis
