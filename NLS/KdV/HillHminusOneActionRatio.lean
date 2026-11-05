import NLS.KdV.HillHminusOneComplexContourActions
import NLS.ComplexAnalysis.ParametricSemicircleMean

/-! # The intrinsic analytic normalized high Hill action ratio

Symmetric coefficients of the actual contour polynomial give the
midpoint and squared half-gap. An even semicircle mean defines the ratio
without gap division and remains analytic through a collapsed gap.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

def hillHminusGapMidpoint (n : ℕ+) (r : ℝ) (q : PeriodOneHminusOne) : ℂ :=
  (hillHminusGapPolynomial n r (0,q)-hillHminusGapPolynomial n r (1,q)+1)/2

def hillHminusSquaredHalfGap (n : ℕ+) (r : ℝ) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusGapMidpoint n r q^2-hillHminusGapPolynomial n r (0,q)

def hillHminusNormalizedActionRatio (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) : ℂ :=
  parametricSemicircleMean (hillHminusJointNormalizedGapRoot n r K) (hillHminusGapMidpoint n r)
    (Complex.sqrt (hillHminusSquaredHalfGap n r q),q)

theorem HillHminusHighGapPair.symmetric_gap_data
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℂ}
    (hpair : HillHminusHighGapPair q n r l u) (hr : 0 < r) :
    hillHminusGapMidpoint n r q = (l+u)/2 ∧ hillHminusSquaredHalfGap n r q = ((u-l)/2)^2 := by
  have hm : hillHminusGapMidpoint n r q = (l+u)/2 := by
    rw [hillHminusGapMidpoint,hpair.gapPolynomial_eq hr 0,hpair.gapPolynomial_eq hr 1]
    ring
  refine ⟨hm,?_⟩
  rw [hillHminusSquaredHalfGap,hm,hpair.gapPolynomial_eq hr 0]
  ring

theorem analyticOnNhd_hillHminus_symmetric_gap_data
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (V : Set PeriodOneHminusOne) (hV : IsOpen V)
    (hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u) :
    AnalyticOnNhd ℂ (hillHminusGapMidpoint n r) V ∧
      AnalyticOnNhd ℂ (hillHminusSquaredHalfGap n r) V := by
  have hP := analyticOnNhd_hillHminusGapPolynomial n r hr V hV hpairs
  have h0 : AnalyticOnNhd ℂ (fun a => hillHminusGapPolynomial n r (0,a)) V := by
    intro a ha
    exact (hP (0,a) ⟨mem_univ _,ha⟩).comp (f := fun a => (0,a)) (analyticAt_const.prod analyticAt_id)
  have h1 : AnalyticOnNhd ℂ (fun a => hillHminusGapPolynomial n r (1,a)) V := by
    intro a ha
    exact (hP (1,a) ⟨mem_univ _,ha⟩).comp (f := fun a => (1,a)) (analyticAt_const.prod analyticAt_id)
  have ht : AnalyticOnNhd ℂ (hillHminusGapMidpoint n r) V :=
    ((h0.sub h1).add analyticOnNhd_const).div analyticOnNhd_const (by intro a _; norm_num)
  exact ⟨ht,(ht.pow 2).sub h0⟩

theorem HillHminusHighGapPair.affine_gap_mem_ball
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℂ}
    (hpair : HillHminusHighGapPair q n r l u) (s : ℝ) (hs : s ∈ Icc (-1) 1) :
    (l+u)/2+(u-l)/2*(s : ℂ) ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by
  have hz : (l+u)/2+(u-l)/2*(s : ℂ) ∈ standardRootGapSegment ((l+u)/2) ((u-l)/2) := ⟨s,hs,rfl⟩
  rw [standardRootGapSegment_eq_segment] at hz
  have hl : (l+u)/2-(u-l)/2 = l := by ring
  have hu : (l+u)/2+(u-l)/2 = u := by ring
  rw [hl,hu] at hz
  exact (convex_ball _ _).segment_subset hpair.left_mem hpair.right_mem hz

theorem hillHminusNormalizedActionRatio_eq_mean
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u) :
    hillHminusNormalizedActionRatio n r K q =
      normalizedSemicircleMean (fun a : ℝ => hillHminusJointNormalizedGapRoot n r K
        ((l+u)/2+(u-l)/2*(a : ℂ),q)) := by
  unfold hillHminusNormalizedActionRatio
  rw [parametricSemicircleMean_eq_of_sq_eq _ _ _ ((u-l)/2) q
    ((complex_sqrt_sq _).trans (hpair.symmetric_gap_data hr).2)]
  dsimp only [parametricSemicircleMean]
  rw [(hpair.symmetric_gap_data hr).1]

theorem analyticOnNhd_hillHminusNormalizedActionRatio
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (V : Set PeriodOneHminusOne) (hV : IsOpen V)
    (K : ℂ × PeriodOneHminusOne → ℂ)
    (hJ : AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V))
    (hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u) :
    AnalyticOnNhd ℂ (hillHminusNormalizedActionRatio n r K) V := by
  obtain ⟨ht,hg⟩ := analyticOnNhd_hillHminus_symmetric_gap_data n r hr V hV hpairs
  intro a ha
  apply analyticAt_parametricSemicircleMean_of_analytic_square
    (hillHminusJointNormalizedGapRoot n r K) (hillHminusGapMidpoint n r)
    (fun b => Complex.sqrt (hillHminusSquaredHalfGap n r b)) _ (isOpen_ball.prod hV) hJ a (ht a ha)
    (by simpa only [complex_sqrt_sq] using hg a ha)
  intro θ _
  refine ⟨?_,ha⟩
  obtain ⟨l,u,hpair⟩ := hpairs a ha
  have he : (Complex.sqrt (hillHminusSquaredHalfGap n r a))^2 = ((u-l)/2)^2 :=
    (complex_sqrt_sq _).trans (hpair.symmetric_gap_data hr).2
  rw [(hpair.symmetric_gap_data hr).1]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with heq | heq
  · rw [heq]
    exact hpair.affine_gap_mem_ball _ ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩
  · rw [heq]
    have hx := hpair.affine_gap_mem_ball (-Real.cos θ)
      ⟨by linarith [Real.cos_le_one θ],by linarith [Real.neg_one_le_cos θ]⟩
    simpa only [ofReal_neg,mul_neg,neg_mul] using hx

theorem hillHminusHighContourAction_eq_gap_square_mul_ratio
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (htrace : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      squaredCosh (K (z,q)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z/2)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u))
    (hw : Γ.windingIntegral ((l+u)/2) = 1) :
    hillHminusHighContourAction n r K q l u Γ =
      (u-l)^2/(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusNormalizedActionRatio n r K q := by
  rw [hillHminusHighContourAction_circuit_formula n r hr K q l u hpair hS hf htrace Γ hΓ,hw,mul_one,
    hillHminusNormalizedActionRatio_eq_mean n r hr K q l u hpair]

theorem norm_hillHminusNormalizedActionRatio_sub_one_le
    (n : ℕ+) (r epsilon : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)))
    (hnorm : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,q)-1‖ ≤ epsilon) :
    ‖hillHminusNormalizedActionRatio n r K q-1‖ ≤ epsilon := by
  rw [hillHminusNormalizedActionRatio_eq_mean n r hr K q l u hpair]
  apply norm_normalizedSemicircleMean_sub_one_le
  · intro a ha
    exact ((hS _ (hpair.affine_gap_mem_ball a ha)).continuousAt.comp
      (f := fun a : ℝ => (l+u)/2+(u-l)/2*(a : ℂ)) (by fun_prop)).continuousWithinAt
  · intro a ha
    exact hnorm _ (hpair.affine_gap_mem_ball a ha)

theorem hillHminusHighContourAction_eq_zero_iff_gap_collapsed
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (htrace : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      squaredCosh (K (z,q)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z/2)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u))
    (hw : Γ.windingIntegral ((l+u)/2) = 1)
    (hR : ‖hillHminusNormalizedActionRatio n r K q-1‖ < 1) :
    hillHminusHighContourAction n r K q l u Γ = 0 ↔ l = u := by
  have hn : hillHminusNormalizedActionRatio n r K q ≠ 0 := by
    intro he
    simp only [he,zero_sub,norm_neg,norm_one,lt_self_iff_false] at hR
  have hc : (8*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 := by simp [Real.pi_ne_zero,n.ne_zero]
  rw [hillHminusHighContourAction_eq_gap_square_mul_ratio n r hr K q l u hpair hS hf htrace Γ hΓ hw]
  constructor
  · intro he
    have hnum : (u-l)^2 = 0 := (div_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_right hn)).resolve_right hc
    have hh : u-l = 0 := sq_eq_zero_iff.mp hnum
    exact (sub_eq_zero.mp hh).symm
  · intro he
    simp [he]

end NLS.KdV
