import NLS.SequenceSpaces.WeightedAnalyticRealization
import NLS.ComplexAnalysis.BanachTaylorBounds

/-! # Weighted Cauchy derivative bounds

Coordinatewise analytic functions with a common weighted norm bound have a derivative in the same weighted space.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A fixed-radius holomorphic ball bound gives a derivative sequence
in the same weighted space, with the explicit Cauchy bound 2M/r. -/
theorem exists_deriv_coeff_of_analytic_ball_bound
    (w : Weight) (f : ℂ → ℤ → ℂ) (r M : ℝ) (hr : 0 < r)
    (ha : ∀ n, AnalyticOnNhd ℂ (fun z => f z n) (ball 0 r))
    (hb : ∀ z ∈ ball (0:ℂ) r, ∃ b : WeightedCoeff w p,
      (∀ n, b.val n = f z n) ∧ ‖b‖ ≤ M) :
    ∃ D : WeightedCoeff w p,
      (∀ n, D.val n = deriv (fun z => f z n) 0) ∧ ‖D‖ ≤ 2*M/r := by
  obtain ⟨hga,hg⟩ := analytic_realization_of_bound w f isOpen_ball ha M hb
  let g (z : ℂ) := ofFunctionOrZero w p (f z)
  have h0 : (0:ℂ) ∈ ball 0 r := mem_ball_self hr
  have hdiff : DifferentiableAt ℂ g 0 := (hga 0 h0).differentiableAt
  have hgn (z : ℂ) (hz : z ∈ ball 0 r) : ‖g z‖ ≤ M := (hg z hz).1
  have hmaps : MapsTo g (ball (0:ℂ) r) (closedBall (g 0) (2*M)) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hgn z hz,hgn 0 h0])
  have hder : ‖fderiv ℂ g 0‖ ≤ 2*M/r :=
    Complex.norm_fderiv_le_div_of_mapsTo_ball hga.differentiableOn hmaps hr
  let D := (fderiv ℂ g 0) 1
  refine ⟨D,?_,?_⟩
  · intro n
    have hd : HasDerivAt (fun z => (g z).val n) (D.val n) 0 :=
      ((evalCLM w p n).hasFDerivAt.comp 0 hdiff.hasFDerivAt).hasDerivAt
    have he : (fun z => f z n) =ᶠ[𝓝 (0:ℂ)] (fun z => (g z).val n) := by
      filter_upwards [isOpen_ball.mem_nhds h0] with z hz
      exact ((hg z hz).2 n).symm
    exact (hd.congr_of_eventuallyEq he).deriv.symm
  · exact ((fderiv ℂ g 0).le_opNorm 1).trans (by simpa only [norm_one,mul_one] using hder)

end NLS.WeightedCoeff
