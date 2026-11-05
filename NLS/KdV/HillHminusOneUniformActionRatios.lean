import NLS.KdV.HillHminusOneActionRatio

/-! # Uniform analytic normalized action ratios for complex high Hill gaps

The ratio is intrinsic, analytic through every collapsed gap, and
uniformly close to one on one complex source neighborhood before all
high indices. Every winding-one local contour has the exact gap-square
factorization. Global gluing between different square charts is separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_uniform_analytic_action_ratios (q : PeriodOneHminusOne) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant t.2 t.1/2) ∧
        (∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
          K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
          (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) ∧
        AnalyticOnNhd ℂ (hillHminusNormalizedActionRatio n r K) V ∧
        ∀ a ∈ V, ‖hillHminusNormalizedActionRatio n r K a-1‖ ≤ epsilon ∧
          hillHminusNormalizedActionRatio n r K a ≠ 0 ∧
          ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
          ∃ Γ₀ : PiecewiseC1Loop,
            Γ₀.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u) ∧
            Γ₀.windingIntegral ((l+u)/2) = 1 ∧
            ∀ Γ : PiecewiseC1Loop,
              Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u) →
              Γ.windingIntegral ((l+u)/2) = 1 →
              hillHminusHighContourAction n r K a l u Γ =
                (u-l)^2/(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusNormalizedActionRatio n r K a ∧
              (hillHminusHighContourAction n r K a l u Γ = 0 ↔ l = u) := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillHminus_normalized_gap_squares q
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon
  let eta : ℝ := min (1/2) epsilon
  have heta : 0 < eta := lt_min (by norm_num) hepsilon
  have heta1 : eta < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hetaε : eta ≤ epsilon := min_le_right _ _
  obtain ⟨N,V,hN,hV,hq,hfamily⟩ := hfamily eta heta
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,_,hrel,_,hmatch,hpairs⟩ := hfamily n hn
  have hdata : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
      (∀ z : ℂ, K (z,a) = (z-l)*(z-u)*twoRootDeflation (fun w => K (w,a)) l u z) ∧
      ∀ z ∈ hillHminusGapSquareDisc n r,
        ‖hillHminusNormalizedGapSquare n K a l u z-1‖ ≤ eta := by
    intro a ha
    obtain ⟨l,u,hpair,_,hfactor,hnorm⟩ := hpairs a ha
    exact ⟨l,u,hpair,hfactor,hnorm⟩
  obtain ⟨hJ,hproperties⟩ := hillHminusJointNormalizedGapRoot_properties n r eta hr heta1 V hV K hK hdata
  have hpairs' : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u := by
    intro a ha
    obtain ⟨l,u,hpair,_⟩ := hpairs a ha
    exact ⟨l,u,hpair⟩
  refine ⟨K,hK,hrel,hmatch,hJ,analyticOnNhd_hillHminusNormalizedActionRatio n r hr V hV K hJ hpairs',?_⟩
  intro a ha
  obtain ⟨l,u,hpair,_⟩ := hpairs a ha
  have hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,a) = -hillHminusGapPolynomial n r (z,a)*hillHminusJointNormalizedGapRoot n r K (z,a)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2) :=
    fun z hz => (hproperties (z,a) ⟨hz,ha⟩).2.2
  have hnorm : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,a)-1‖ ≤ eta :=
    fun z hz => (hproperties (z,a) ⟨hz,ha⟩).2.1
  have hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,a))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) := by
    intro z hz
    exact (hJ (z,a) ⟨hz,ha⟩).comp (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  have htrace : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      squaredCosh (K (z,a)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant a z/2 :=
    fun z hz => hrel (z,a) ⟨ball_subset_closedBall hz,ha⟩
  have hR := norm_hillHminusNormalizedActionRatio_sub_one_le n r eta hr K a l u hpair hS hnorm
  have hR1 : ‖hillHminusNormalizedActionRatio n r K a-1‖ < 1 := hR.trans_lt heta1
  have hnz : hillHminusNormalizedActionRatio n r K a ≠ 0 := by
    intro he
    simp only [he,zero_sub,norm_neg,norm_one,lt_self_iff_false] at hR1
  obtain ⟨Γ₀,hin,hw⟩ := hpair.exists_winding_one_contour
  refine ⟨hR.trans hetaε,hnz,l,u,hpair,Γ₀,hin,hw,?_⟩
  intro Γ hΓ hΓw
  exact ⟨hillHminusHighContourAction_eq_gap_square_mul_ratio n r hr K a l u hpair hS hf htrace Γ hΓ hΓw,
    hillHminusHighContourAction_eq_zero_iff_gap_collapsed n r hr K a l u hpair hS hf htrace Γ hΓ hΓw hR1⟩

end NLS.KdV
