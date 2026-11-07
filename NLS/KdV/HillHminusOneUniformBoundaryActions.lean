import NLS.KdV.HillHminusOneBoundaryAction

/-! # Locally uniform actual real-gap boundary action normalization

One radius precedes the accuracy, and one complex H-minus-one neighborhood
and cutoff precede every high index and every real potential in that
neighborhood. The actual primitive boundary limits and the literal gap
integral have the same filled square and spectral pair. This does not
yet identify the boundary integral with the original contour action.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_uniform_gap_boundary_actions (q : PeriodOneHminusOne) :
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
        ∀ a ∈ V, IsRealPeriodOneHminusOne a → ∃ l u : ℝ, l ≤ u ∧
          HillHminusHighGapPair a n r (l : ℂ) (u : ℂ) ∧
          IntervalIntegrable (fun x : ℝ => Complex.sqrt (K ((x : ℂ),a))) volume l u ∧
          ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusGapBoundaryAction K a l u-
            (((u-l : ℝ) : ℂ)^2)‖ ≤ (u-l)^2*epsilon ∧
          ∀ x ∈ Icc l u,
            Tendsto (fun y : ℝ => hillHminusContinuedPrimitive ((x : ℂ)+(y : ℂ)*I,a)+I*(n : ℂ)*Real.pi)
              (𝓝[>] 0) (𝓝 (Complex.sqrt (K ((x : ℂ),a)))) ∧
            Tendsto (fun y : ℝ => hillHminusContinuedPrimitive ((x : ℂ)-(y : ℂ)*I,a)+I*(n : ℂ)*Real.pi)
              (𝓝[>] 0) (𝓝 (-Complex.sqrt (K ((x : ℂ),a)))) := by
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
  refine ⟨K,hK,hbound,hrel,hzero,hmatch,hJ,?_⟩
  intro a ha hareal
  obtain ⟨l₀,u₀,hpair₀,_⟩ := hpairs a ha
  obtain ⟨l,u,hlu,hpair⟩ := hpair₀.exists_real_ordered hareal
  have hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,a) = -hillHminusGapPolynomial n r (z,a)*hillHminusJointNormalizedGapRoot n r K (z,a)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2) :=
    fun z hz => (hproperties (z,a) ⟨hz,ha⟩).2.2
  have hnorm : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,a)-1‖ ≤ eta :=
    fun z hz => (hproperties (z,a) ⟨hz,ha⟩).2.1
  obtain ⟨hint,_,herror⟩ := hillHminusGapBoundaryAction_properties n r eta hr heta1 V K hJ
    a ha l u hlu hpair hf hnorm
  refine ⟨l,u,hlu,hpair,hint,herror.trans (mul_le_mul_of_nonneg_left hetaε (sq_nonneg _)),?_⟩
  intro x hx
  exact tendsto_hillHminusShiftedPrimitive_sqrt_boundaries n r V K hK hmatch a ha hareal x
    (hpair.real_gap_mem_ball x hx)
    (hillHminus_real_gap_sqrt_continuousAt n r eta hr heta1 K a l u hpair hf hnorm x hx)

end NLS.KdV
