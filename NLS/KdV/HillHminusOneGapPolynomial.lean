import NLS.KdV.HillHminusOnePairUniqueness
import NLS.ComplexAnalysis.TwoRootCircleMoments

/-! # The intrinsic analytic high Hill gap polynomial

Fixed contours of the actual H-minus-one radicand recover the monic
quadratic factor. This definition has no chosen root ordering and remains
jointly analytic through a collapsed gap.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusGapPolynomial (n : ℕ+) (r : ℝ) : ℂ × PeriodOneHminusOne → ℂ :=
  momentPairPolynomial (fun t => hillHminusRadicand t.2 t.1)
    (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)

theorem HillHminusHighGapPair.radicand_ne_zero_on_sphere
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℂ}
    (h : HillHminusHighGapPair q n r l u)
    (z : ℂ) (hz : z ∈ sphere (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) :
    hillHminusRadicand q z ≠ 0 := by
  intro he
  rcases (h.zeros_iff z (sphere_subset_closedBall hz)).mp he with rfl | rfl
  · exact sphere_disjoint_ball.le_bot ⟨hz,h.left_mem⟩
  · exact sphere_disjoint_ball.le_bot ⟨hz,h.right_mem⟩

/-- Actual logarithmic moments count both physical roots with their full multiplicity. -/
theorem HillHminusHighGapPair.logarithmicCircleMoment_eq
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℂ}
    (h : HillHminusHighGapPair q n r l u) (hr : 0 < r) (k : ℕ) :
    logarithmicCircleMoment (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1)
      (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) k q = l^k+u^k := by
  apply logarithmicCircleMoment_eq_pair
    (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1) _ _ (by positivity) q l u
    ?_ h.left_mem h.right_mem h.zeros_iff h.multiplicity k
  intro z _
  exact (analyticOnNhd_hillHminusRadicand_joint (z,q) (mem_univ _)).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

/-- The intrinsic polynomial is the actual two-root factor for every valid pair. -/
theorem HillHminusHighGapPair.gapPolynomial_eq
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℂ}
    (h : HillHminusHighGapPair q n r l u) (hr : 0 < r) (z : ℂ) :
    hillHminusGapPolynomial n r (z,q) = (z-l)*(z-u) := by
  exact momentPairPolynomial_eq _ _ _ q l u z
    (by simpa only [pow_one] using h.logarithmicCircleMoment_eq hr 1)
    (h.logarithmicCircleMoment_eq hr 2)

theorem HillHminusHighGapPair.gapPolynomial_ne_zero_on_sphere
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℂ}
    (h : HillHminusHighGapPair q n r l u) (hr : 0 < r)
    (z : ℂ) (hz : z ∈ sphere (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) :
    hillHminusGapPolynomial n r (z,q) ≠ 0 := by
  rw [h.gapPolynomial_eq hr z]
  exact mul_ne_zero
    (sub_ne_zero.mpr (fun he => sphere_disjoint_ball.le_bot ⟨he ▸ hz,h.left_mem⟩))
    (sub_ne_zero.mpr (fun he => sphere_disjoint_ball.le_bot ⟨he ▸ hz,h.right_mem⟩))

theorem analyticOnNhd_hillHminusGapPolynomial (n : ℕ+) (r : ℝ) (hr : 0 < r)
    (V : Set PeriodOneHminusOne) (hV : IsOpen V)
    (hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u) :
    AnalyticOnNhd ℂ (hillHminusGapPolynomial n r) (univ ×ˢ V) := by
  apply analyticOnNhd_momentPairPolynomial _ analyticOnNhd_hillHminusRadicand_joint
    _ _ (by positivity) V hV
  intro a ha z hz
  obtain ⟨l,u,hpair⟩ := hpairs a ha
  exact hpair.radicand_ne_zero_on_sphere z hz

end NLS.KdV
