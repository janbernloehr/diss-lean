import NLS.ComplexAnalysis.BanachHolomorphicLineBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Scaling of Banach-valued line Taylor jets

The Taylor jets of a holomorphic curve scale homogeneously when its
complex parameter is rescaled. A disc assumption suffices; behavior
of the curve outside that disc is irrelevant.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- On a complex disc, the `k`-th Taylor derivative at zero scales
by the `k`-th power of a scalar contraction. -/
theorem iteratedDeriv_comp_const_mul_of_contDiffOn_ball
    (g : ℂ → F) (r : ℝ) (hr : 0 < r) (k : ℕ)
    (hg : ContDiffOn ℂ k g (ball 0 r))
    (c : ℂ) (hc : ‖c‖ ≤ 1) :
    iteratedDeriv k (fun z : ℂ => g (c*z)) 0 =
      c^k • iteratedDeriv k g 0 := by
  have hmap : MapsTo (fun z : ℂ => c*z) (ball 0 r) (ball 0 r) := by
    intro z hz
    have hz' : ‖z‖ < r := by
      simpa only [mem_ball, dist_zero_right] using hz
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
    have hmul : ‖c‖*‖z‖ ≤ ‖z‖ := by nlinarith
    simpa only [mem_ball, dist_zero_right, norm_mul] using
      (hmul.trans_lt hz')
  have hscale := iteratedDerivWithin_comp_const_smul
    (x := (0 : ℂ)) (s := ball 0 r)
      (mem_ball_self hr) isOpen_ball.uniqueDiffOn hg c hmap
  rw [iteratedDerivWithin_of_isOpen isOpen_ball
    (mem_ball_self hr), mul_zero,
    iteratedDerivWithin_of_isOpen isOpen_ball
      (mem_ball_self hr)] at hscale
  exact hscale

end NLS.ComplexAnalysis
