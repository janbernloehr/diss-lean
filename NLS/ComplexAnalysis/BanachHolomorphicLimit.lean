import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Uniform holomorphic limits on complex normed spaces

Schwarz estimates control the full Fréchet derivative on a smaller ball by
the function on a larger ball. Uniform convergence on an actual neighborhood
therefore gives uniform derivative convergence and complex differentiability
of the limit, also for infinite-dimensional domains.
-/

noncomputable section
open Filter Topology Metric
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A uniform difference bound controls the operator norm of the derivative difference on a smaller ball. -/
theorem norm_fderiv_sub_le_of_bound (f g : E → F) (c x : E) (r δ : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c (2*r))) (hg : DifferentiableOn ℂ g (ball c (2*r)))
    (hb : ∀ y ∈ ball c (2*r), ‖f y-g y‖ ≤ δ) (hx : x ∈ ball c r) :
    ‖fderiv ℂ f x-fderiv ℂ g x‖ ≤ 2*δ/r := by
  have hsub : ball x r ⊆ ball c (2*r) := by
    intro y hy
    have h := dist_triangle y x c
    rw [mem_ball] at hy hx ⊢
    linarith
  have hxc : x ∈ ball c (2*r) := hsub (mem_ball_self hr)
  have hfx := (hf x hxc).differentiableAt (isOpen_ball.mem_nhds hxc)
  have hgx := (hg x hxc).differentiableAt (isOpen_ball.mem_nhds hxc)
  rw [← fderiv_sub hfx hgx]
  apply Complex.norm_fderiv_le_div_of_mapsTo_ball ((hf.sub hg).mono hsub) _ hr
  intro y hy
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_sub_le _ _).trans (by simpa only [two_mul, Pi.sub_apply] using add_le_add (hb y (hsub hy)) (hb x hxc))

/-- Uniformly Cauchy holomorphic functions have uniformly Cauchy Fréchet derivatives on smaller balls. -/
theorem uniformCauchySeqOn_fderiv_ball (u : ℕ → E → F) (c : E) (r : ℝ) (hr : 0 < r)
    (hu : ∀ᶠ n in atTop, DifferentiableOn ℂ (u n) (ball c (2*r)))
    (hC : UniformCauchySeqOn u atTop (ball c (2*r))) :
    UniformCauchySeqOn (fun n => fderiv ℂ (u n)) atTop (ball c r) := by
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hu
  rw [Metric.uniformCauchySeqOn_iff] at hC ⊢
  intro ε hε
  obtain ⟨N,hN⟩ := hC (ε*r/4) (by positivity)
  refine ⟨max N J,fun m hm n hn x hx => ?_⟩
  rw [dist_eq_norm]
  have hb := norm_fderiv_sub_le_of_bound (u m) (u n) c x r (ε*r/4) hr
    (hJ m ((le_max_right _ _).trans hm)) (hJ n ((le_max_right _ _).trans hn))
    (fun y hy => by simpa only [dist_eq_norm] using
      (hN m ((le_max_left _ _).trans hm) n ((le_max_left _ _).trans hn) y hy).le) hx
  apply hb.trans_lt
  have he : 2*(ε*r/4)/r = ε/2 := by field_simp; ring
  rw [he]
  exact half_lt_self hε

variable [CompleteSpace F]

/-- Uniform convergence on a ball gives a derivative of the limit and uniform operator-norm convergence. -/
theorem hasFDerivAt_uniformLimit_ball (u : ℕ → E → F) (f : E → F) (c : E) (r : ℝ) (hr : 0 < r)
    (hu : ∀ᶠ n in atTop, DifferentiableOn ℂ (u n) (ball c (2*r)))
    (hf : TendstoUniformlyOn u f atTop (ball c (2*r))) :
    ∃ g : E → E →L[ℂ] F,
      TendstoUniformlyOn (fun n => fderiv ℂ (u n)) g atTop (ball c r) ∧
      ∀ x ∈ ball c r, HasFDerivAt f (g x) x := by
  have hc := uniformCauchySeqOn_fderiv_ball u c r hr hu hf.uniformCauchySeqOn
  let g (x : E) : E →L[ℂ] F := limUnder atTop (fun n => fderiv ℂ (u n) x)
  have hg : TendstoUniformlyOn (fun n => fderiv ℂ (u n)) g atTop (ball c r) :=
    hc.tendstoUniformlyOn_of_tendsto (fun x hx => (hc.cauchySeq hx).tendsto_limUnder)
  refine ⟨g,hg,fun x hx => ?_⟩
  have hball : ball c r ∈ 𝓝 x := isOpen_ball.mem_nhds hx
  have hsub : ball c r ⊆ ball c (2*r) := ball_subset_ball (by linarith)
  apply hasFDerivAt_of_tendstoUniformlyOnFilter
    (hg.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr hball))
  · have he := hu.prod_mk (show ∀ᶠ y in 𝓝 x, y ∈ ball c r from hball)
    filter_upwards [he] with t ht
    exact ((ht.1 t.2 (hsub ht.2)).differentiableAt (isOpen_ball.mem_nhds (hsub ht.2))).hasFDerivAt
  · filter_upwards [hball] with y hy
    exact hf.tendsto_at (hsub hy)

/-- Identify the uniform derivative limit with the actual Fréchet derivative. -/
theorem tendstoUniformlyOn_fderiv_ball (u : ℕ → E → F) (f : E → F) (c : E) (r : ℝ) (hr : 0 < r)
    (hu : ∀ᶠ n in atTop, DifferentiableOn ℂ (u n) (ball c (2*r)))
    (hf : TendstoUniformlyOn u f atTop (ball c (2*r))) :
    DifferentiableOn ℂ f (ball c r) ∧
      TendstoUniformlyOn (fun n => fderiv ℂ (u n)) (fderiv ℂ f) atTop (ball c r) := by
  obtain ⟨g,hg,hd⟩ := hasFDerivAt_uniformLimit_ball u f c r hr hu hf
  exact ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt,
    hg.congr_right (fun x hx => (hd x hx).fderiv.symm)⟩

end NLS.ComplexAnalysis
