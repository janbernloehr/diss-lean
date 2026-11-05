import NLS.KdV.HillHminusOneContourBoundaryAction

/-! # Native high Hill action contours, including collapsed gaps

Noncollapsed real gaps admit shrinking positively oriented ellipses.
Collapsed gaps admit small positively oriented circles, whose action
vanishes because the local primitive extends through the double endpoint.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem hillHminusHighContourAction_collapsed_eq_zero
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l : ℂ) (hpair : HillHminusHighGapPair q n r l l)
    (hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (htrace : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      squaredCosh (K (z,q)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z/2)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l l)) :
    hillHminusHighContourAction n r K q l l Γ = 0 := by
  have he : hillHminusOffGapPrimitive n r K q l l =
      (fun z => I/(2*((Real.pi : ℂ)*(n : ℕ)))*(l-z)*hillHminusJointNormalizedGapRoot n r K (z,q)) := by
    funext z
    simp [hillHminusOffGapPrimitive]
  have hF : AnalyticOnNhd ℂ (hillHminusOffGapPrimitive n r K q l l)
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) := by
    rw [he]
    exact (analyticOnNhd_const.mul (analyticOnNhd_const.sub analyticOnNhd_id)).mul hS
  rw [hillHminusHighContourAction_eq_neg_primitive_period n r hr K q l l hpair hS hf htrace Γ hΓ,
    Γ.integral_eq_zero_of_convex _ _ isOpen_ball (convex_ball _ _) hF.differentiableOn
      (fun i t => (hΓ i t).1),mul_zero]

theorem exists_hillHminus_high_contour_action
    (n : ℕ+) (r epsilon : ℝ) (hr : 0 < r) (hepsilon : epsilon < 1)
    (V : Set PeriodOneHminusOne) (K : ℂ × PeriodOneHminusOne → ℂ)
    (hJ : AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V))
    (q : PeriodOneHminusOne) (hqV : q ∈ V) (l u : ℝ) (hlu : l ≤ u)
    (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (hnorm : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,q)-1‖ ≤ epsilon)
    (htrace : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      squaredCosh (K (z,q)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z/2) :
    ∃ Γ : PiecewiseC1Loop,
      Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ (l : ℂ) (u : ℂ)) ∧
      Γ.windingIntegral (((l+u)/2 : ℝ) : ℂ) = 1 ∧
      hillHminusHighContourAction n r K q (l : ℂ) (u : ℂ) Γ = hillHminusGapBoundaryAction K q l u := by
  rcases lt_or_eq_of_le hlu with hlt | heq
  · obtain ⟨R,hR,hperiod⟩ := exists_hillHminus_contour_eq_gap_boundary_action n r epsilon hr hepsilon
      V K hJ q hqV l u hlt hpair hf hnorm htrace
    exact ⟨_,hperiod ((1+R)/2) (by linarith) (by linarith)⟩
  · subst u
    let U : Set ℂ := ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)
    have hl : (l : ℂ) ∈ U := hpair.left_mem
    obtain ⟨e,he,hball⟩ := Metric.isOpen_iff.mp isOpen_ball (l : ℂ) hl
    let rho : ℝ := e/2
    have hrho : 0 < rho := half_pos he
    have hclosed : closedBall (l : ℂ) rho ⊆ U := by
      intro z hz
      apply hball
      apply mem_ball.mpr
      have hd := mem_closedBall.mp hz
      dsimp [rho] at hd
      linarith
    let Γ := PiecewiseC1Loop.circle (l : ℂ) rho
    have hin : Γ.Inside (U \ segment ℝ (l : ℂ) (l : ℂ)) := by
      intro i t
      have hs : Γ.edge i t ∈ sphere (l : ℂ) rho :=
        circleMap_mem_sphere (l : ℂ) hrho.le ((2*Real.pi)*(t : ℝ))
      refine ⟨hclosed (sphere_subset_closedBall hs),?_⟩
      rw [segment_same,mem_singleton_iff]
      intro heq
      have hd := mem_sphere.mp hs
      rw [heq,dist_self] at hd
      linarith
    have hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q)) U := by
      intro z hz
      exact (hJ (z,q) ⟨hz,hqV⟩).comp (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
    refine ⟨Γ,hin,?_,?_⟩
    · simpa using PiecewiseC1Loop.windingIntegral_circle (l : ℂ) (l : ℂ) rho (by simpa using hrho)
    · rw [hillHminusHighContourAction_collapsed_eq_zero n r hr K q (l : ℂ) hpair hS hf htrace Γ hin]
      simp [hillHminusGapBoundaryAction]

end NLS.KdV
