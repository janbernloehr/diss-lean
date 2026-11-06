import NLS.KdV.HillHminusOneJointGapQuotient

/-! # Intrinsic joint analytic normalization through high Hill gaps

The symmetric contour polynomial and Cauchy reconstruction remove the
dependence on chosen endpoint labels. The root is jointly analytic in
the energy and complex H-minus-one potential, including collapsed gaps,
and retains the exact original primitive-square normalization.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusJointNormalizedGapRoot_properties
    (n : ℕ+) (r epsilon : ℝ) (hr : 0 < r) (hepsilon : epsilon < 1)
    (V : Set PeriodOneHminusOne) (hV : IsOpen V)
    (K : ℂ × PeriodOneHminusOne → ℂ)
    (hK : AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V))
    (hdata : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
      (∀ z : ℂ, K (z,a) = (z-l)*(z-u)*twoRootDeflation (fun w => K (w,a)) l u z) ∧
      ∀ z ∈ hillHminusGapSquareDisc n r,
        ‖hillHminusNormalizedGapSquare n K a l u z-1‖ ≤ epsilon) :
    AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) ∧
    ∀ t ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V,
      hillHminusJointNormalizedGapRoot n r K t ≠ 0 ∧
      ‖hillHminusJointNormalizedGapRoot n r K t-1‖ ≤ epsilon ∧
      K t = -hillHminusGapPolynomial n r t*hillHminusJointNormalizedGapRoot n r K t^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2) := by
  have hf (a : PeriodOneHminusOne) (ha : a ∈ V) :
      AnalyticOnNhd ℂ (fun w => K (w,a)) (hillHminusGapSquareDisc n r) := by
    intro z hz
    exact (hK (z,a) ⟨hz,ha⟩).comp
      (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  have hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u := by
    intro a ha
    obtain ⟨l,u,hpair,_,_⟩ := hdata a ha
    exact ⟨l,u,hpair⟩
  have hJ : AnalyticOnNhd ℂ (hillHminusJointNormalizedGapSquare n r K)
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) :=
    analyticOnNhd_const.mul (analyticOnNhd_hillHminusJointGapQuotient n r hr V hV K hK hpairs)
  have hb (t : ℂ × PeriodOneHminusOne)
      (ht : t ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) :
      ‖hillHminusJointNormalizedGapSquare n r K t-1‖ ≤ epsilon := by
    obtain ⟨l,u,hpair,hfactor,hnorm⟩ := hdata t.2 ht.2
    rw [show t = (t.1,t.2) from rfl,
      hillHminusJointNormalizedGapSquare_eq n r hr K t.2 l u hpair (hf t.2 ht.2) hfactor t.1 ht.1]
    exact hnorm t.1 (ball_subset_closedBall ht.1)
  refine ⟨analyticOnNhd_principalSqrt_of_norm_sub_one_lt_one _ _ hJ
    (fun t ht => (hb t ht).trans_lt hepsilon), ?_⟩
  intro t ht
  have hnorm : ‖hillHminusJointNormalizedGapRoot n r K t-1‖ ≤ epsilon :=
    (norm_principalSqrt_sub_one_le _).trans (hb t ht)
  have hne : hillHminusJointNormalizedGapRoot n r K t ≠ 0 := by
    intro he
    rw [he,zero_sub,norm_neg,norm_one] at hnorm
    linarith
  refine ⟨hne,hnorm,?_⟩
  obtain ⟨l,u,hpair,hfactor,_⟩ := hdata t.2 ht.2
  have heq := hillHminusJointNormalizedGapSquare_eq n r hr K t.2 l u hpair
    (hf t.2 ht.2) hfactor t.1 ht.1
  have hsq : hillHminusJointNormalizedGapRoot n r K t^2 =
      hillHminusNormalizedGapSquare n K t.2 l u t.1 := (complex_sqrt_sq _).trans heq
  calc
    K t = -(t.1-l)*(t.1-u)*hillHminusNormalizedGapSquare n K t.2 l u t.1 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2) := by
      have he := hillHminusNormalizedGapRoot_factor n K t.2 l u hfactor t.1
      rw [hillHminusNormalizedGapRoot_sq] at he
      exact he
    _ = _ := by
      rw [hpair.gapPolynomial_eq hr t.1, hsq]
      ring

/-- One actual primitive-square family has an intrinsic jointly analytic
normalized root, with a common H-minus-one neighborhood before all high
indices, all nearby potentials and every point of each open energy disc. -/
theorem exists_hillHminus_joint_normalized_gap_roots (q : PeriodOneHminusOne) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V, ‖K t‖ < 1) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant t.2 t.1/2) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          K t = 0 ↔ hillHminusRadicand t.2 t.1 = 0) ∧
        (∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
          K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
          (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) ∧
        ∀ t ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V,
          hillHminusJointNormalizedGapRoot n r K t ≠ 0 ∧
          ‖hillHminusJointNormalizedGapRoot n r K t-1‖ ≤ epsilon ∧
          K t = -hillHminusGapPolynomial n r t*hillHminusJointNormalizedGapRoot n r K t^2 /
            (4*((Real.pi : ℂ)*(n : ℕ))^2) := by
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
  obtain ⟨K,hK,hbound,hrel,hzero,hmatch,hpairs⟩ := hfamily n hn
  have hdata : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
      (∀ z : ℂ, K (z,a) = (z-l)*(z-u)*twoRootDeflation (fun w => K (w,a)) l u z) ∧
      ∀ z ∈ hillHminusGapSquareDisc n r,
        ‖hillHminusNormalizedGapSquare n K a l u z-1‖ ≤ eta := by
    intro a ha
    obtain ⟨l,u,hpair,_,hfactor,hnorm⟩ := hpairs a ha
    exact ⟨l,u,hpair,hfactor,hnorm⟩
  obtain ⟨hJ,hproperties⟩ := hillHminusJointNormalizedGapRoot_properties n r eta hr heta1 V hV K hK hdata
  exact ⟨K,hK,hbound,hrel,hzero,hmatch,hJ,fun t ht =>
    ⟨(hproperties t ht).1, (hproperties t ht).2.1.trans hetaε, (hproperties t ht).2.2⟩⟩

end NLS.KdV
