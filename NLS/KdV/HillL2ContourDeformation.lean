import NLS.KdV.HillL2HighContourMoments

/-! # Annular contour independence for actual high Hill moments

The localization bound applies along the complete complex potential
segment. Consequently every concentric annulus outside radius `4*‖q‖`
and inside the checked radius-n disc lies on the same source-normalized
sheet. Cauchy deformation gives the same physical moment and Arnold
formula on every such circle, at every integer hierarchy level.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2Continuation_high_annulus
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (r R : ℝ) (hr : 4*‖q‖ < r) (hR : R ≤ (n : ℝ))
    (z : ℂ) (hz : z ∈ closedBall (freeHillValue n : ℂ) R \ ball (freeHillValue n : ℂ) r) :
    (z,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by
  have hzR := mem_closedBall.mp hz.1
  have hzr : r ≤ dist z (freeHillValue n : ℂ) := not_lt.mp (by simpa only [mem_ball] using hz.2)
  exact mem_hillL2ContinuationDomain_of_high_distance q hq n hn (by linarith [norm_nonneg q]) z
    (mem_closedBall.mpr (hzR.trans hR)) (by simpa only [dist_eq_norm] using hr.trans_le hzr)

theorem hillL2HighContourMoment_eq_radius
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (r : ℝ) (hr : 4*‖q‖ < r) (hrn : r ≤ (n : ℝ)) (m : ℕ) :
    hillL2HighContourMoment n m (SpectralWeight.one.toCoeff q) =
      -(Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue n : ℂ),r),
        z^m*hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff q) := by
  apply hillL2SourceFamily.contourMoment_eq_of_annulus (freeHillValue n : ℂ) r (n : ℝ)
    (by linarith [norm_nonneg q]) hrn (SpectralWeight.one.toCoeff q)
    (hillL2Continuation_high_annulus q hq n hn hcut r (n : ℝ) hr le_rfl) m

theorem hillL2HighContourMoment_arnold_radius
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (r : ℝ) (hr : 4*‖q‖ < r) (hrn : r ≤ (n : ℝ)) (m : ℕ) :
    hillL2HighContourMoment n m (SpectralWeight.one.toCoeff q) =
      ((m+1 : ℂ)*(Real.pi : ℂ))⁻¹ * ∮ z in C((freeHillValue n : ℂ),r),
        z^(m+1)*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
          hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q) := by
  rw [hillL2HighContourMoment_eq_radius q hq n hn hcut r hr hrn m]
  apply hillL2SourceFamily.contourMoment_arnold (freeHillValue n : ℂ) r
    (by linarith [norm_nonneg q]) (SpectralWeight.one.toCoeff q) _ m
  intro z hz
  apply hillL2Continuation_high_annulus q hq n hn hcut r r hr hrn z
  exact ⟨sphere_subset_closedBall hz,fun h => sphere_disjoint_ball.le_bot ⟨hz,h⟩⟩

theorem hillL2Continued_period_eq_zero_radius
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (r : ℝ) (hr : 4*‖q‖ < r) (hrn : r ≤ (n : ℝ)) :
    (∮ z in C((freeHillValue n : ℂ),r),
      deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
        hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q)) = 0 := by
  apply hillL2SourceFamily.period_eq_zero (freeHillValue n : ℂ) r
    (by linarith [norm_nonneg q]) (SpectralWeight.one.toCoeff q)
  intro z hz
  apply hillL2Continuation_high_annulus q hq n hn hcut r r hr hrn z
  exact ⟨sphere_subset_closedBall hz,fun h => sphere_disjoint_ball.le_bot ⟨hz,h⟩⟩

end NLS.KdV
