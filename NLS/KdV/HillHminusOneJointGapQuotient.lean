import NLS.KdV.HillHminusOneGapPolynomial
import NLS.KdV.HillHminusOneNormalizedGapRoots
import NLS.ComplexAnalysis.JointCircleCauchyTransform

/-! # Jointly analytic intrinsic high Hill gap quotients

The density uses the actual trace's symmetric contour polynomial, so it
has no chosen root ordering. Cauchy reconstruction fills both roots and
is jointly analytic in energy and the original H-minus-one potential.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusJointGapQuotient (n : ℕ+) (r : ℝ)
    (K : ℂ × PeriodOneHminusOne → ℂ) : ℂ × PeriodOneHminusOne → ℂ :=
  jointCircleCauchyTransform (fun t => K t/hillHminusGapPolynomial n r t)
    (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)

def hillHminusJointNormalizedGapSquare (n : ℕ+) (r : ℝ)
    (K : ℂ × PeriodOneHminusOne → ℂ) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  -4*((Real.pi*(n : ℕ) : ℝ) : ℂ)^2*hillHminusJointGapQuotient n r K t

def hillHminusJointNormalizedGapRoot (n : ℕ+) (r : ℝ)
    (K : ℂ × PeriodOneHminusOne → ℂ) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  Complex.sqrt (hillHminusJointNormalizedGapSquare n r K t)

theorem analyticOnNhd_hillHminusJointGapQuotient
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (V : Set PeriodOneHminusOne) (hV : IsOpen V)
    (K : ℂ × PeriodOneHminusOne → ℂ)
    (hK : AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V))
    (hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u) :
    AnalyticOnNhd ℂ (hillHminusJointGapQuotient n r K)
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) := by
  have hP := analyticOnNhd_hillHminusGapPolynomial n r hr V hV hpairs
  have hdensity : AnalyticOnNhd ℂ (fun t => K t/hillHminusGapPolynomial n r t)
      (sphere (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) := by
    intro t ht
    obtain ⟨l,u,hpair⟩ := hpairs t.2 ht.2
    exact (hK t ⟨sphere_subset_closedBall ht.1,ht.2⟩).div (hP t ⟨mem_univ _,ht.2⟩)
      (hpair.gapPolynomial_ne_zero_on_sphere hr t.1 ht.1)
  apply (analyticOnNhd_jointCircleCauchyTransform _ _ _ (by positivity) V hV hdensity).mono
  intro t ht
  exact ⟨fun hw => sphere_disjoint_ball.le_bot ⟨hw,ht.1⟩,ht.2⟩

/-- The intrinsic contour reconstruction equals every valid analytic
two-root deflation, including the filled values at a collapsed pair. -/
theorem hillHminusJointGapQuotient_eq_deflation
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (a : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair a n r l u)
    (hf : AnalyticOnNhd ℂ (fun w => K (w,a)) (hillHminusGapSquareDisc n r))
    (hfactor : ∀ z : ℂ, K (z,a) = (z-l)*(z-u)*twoRootDeflation (fun w => K (w,a)) l u z)
    (z : ℂ) (hz : z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) :
    hillHminusJointGapQuotient n r K (z,a) = twoRootDeflation (fun w => K (w,a)) l u z := by
  apply jointCircleCauchyTransform_eq_filling _ _ _ (by positivity) a _
    (analyticOnNhd_twoRootDeflation _ _ l u hf
      (ball_subset_closedBall hpair.left_mem) (ball_subset_closedBall hpair.right_mem)) ?_ z hz
  intro w hw
  apply (div_eq_iff (hpair.gapPolynomial_ne_zero_on_sphere hr w hw)).mpr
  rw [hpair.gapPolynomial_eq hr w, hfactor w]
  ring

theorem hillHminusJointNormalizedGapSquare_eq
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (a : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair a n r l u)
    (hf : AnalyticOnNhd ℂ (fun w => K (w,a)) (hillHminusGapSquareDisc n r))
    (hfactor : ∀ z : ℂ, K (z,a) = (z-l)*(z-u)*twoRootDeflation (fun w => K (w,a)) l u z)
    (z : ℂ) (hz : z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) :
    hillHminusJointNormalizedGapSquare n r K (z,a) = hillHminusNormalizedGapSquare n K a l u z := by
  change -4*((Real.pi*(n : ℕ) : ℝ) : ℂ)^2*hillHminusJointGapQuotient n r K (z,a) =
    -4*((Real.pi*(n : ℕ) : ℝ) : ℂ)^2*twoRootDeflation (fun w => K (w,a)) l u z
  rw [hillHminusJointGapQuotient_eq_deflation n r hr K a l u hpair hf hfactor z hz]

end NLS.KdV
