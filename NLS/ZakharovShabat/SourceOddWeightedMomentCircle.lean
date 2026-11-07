import NLS.ZakharovShabat.SourceFilledGapQuotientComplex

/-! Odd centered primitive moments vanish on any admissible circle,
with any numerator analytic across the whole selected disc. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W : Set (CoeffPair p)}

theorem odd_weighted_moment_circle_eq_zero
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (l : ℕ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdisc : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (a : ℂ → ℂ) (ha : AnalyticOnNhd ℂ a (closedBall c R)) :
    (∮ z in C(c,R), (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^(2*l+1) *
      (a z/sourceStandardRoot hp hp1 ψ n z)) = 0 := by
  let H : ℂ → ℂ := fun z => I * (sourceFullAbelianSquare hp hp1 W n (z,ψ))^l *
    C.filledGapQuotient n ψ z * a z
  have hH : AnalyticOnNhd ℂ H (closedBall c R) := by
    intro z hz
    have hs := C.fullSquare_analytic n ψ hψ z (fun j hj _ => hdisc hz j hj)
    exact ((analyticAt_const.mul (hs.pow l)).mul
      (C.filledGapQuotient_analytic_complex n ψ hψ z (hdisc hz))).mul (ha z hz)
  have hd : DifferentiableOn ℂ H (closedBall c R) :=
    fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  have hzero := (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn).circleIntegral_eq_zero hR
  calc
    _ = ∮ z in C(c,R), H z := by
      apply circleIntegral.integral_congr hR
      intro z hz
      dsimp only [H]
      rw [show (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^(2*l+1) *
          (a z/sourceStandardRoot hp hp1 ψ n z) =
          ((sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^(2*l+1) /
            sourceStandardRoot hp hp1 ψ n z) * a z by ring,
        C.odd_primitive_div_root_eq_filled n l ψ hψ z (hcircle hz)]
    _ = 0 := hzero

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
