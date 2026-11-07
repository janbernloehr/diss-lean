import NLS.KdV.HillHminusOneContourActionExistence

/-! # Locally uniform high Hill contour action normalization

The radius is chosen before the accuracy; one complex H-minus-one
neighborhood and one cutoff then work for all high indices and all real
potentials in that neighborhood. The root agrees with the actual source
root on both nonreal half-discs. Actual winding-one contour actions equal
the real-gap boundary integral and have the exact eight-pi-n normalization.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_uniform_high_contour_actions (q : PeriodOneHminusOne) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V) ∧
        AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
          (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) ∧
        ∀ a ∈ V, IsRealPeriodOneHminusOne a → ∃ l u : ℝ, l ≤ u ∧
          HillHminusHighGapPair a n r (l : ℂ) (u : ℂ) ∧
          (∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r), z.im ≠ 0 →
            hillHminusOffGapPrimitive n r K a (l : ℂ) (u : ℂ) z =
              hillHminusContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi ∧
            hillHminusOffGapRoot n r K a (l : ℂ) (u : ℂ) z = hillHminusContinuedRoot (z,a)) ∧
          ∃ Γ : PiecewiseC1Loop,
            Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ (l : ℂ) (u : ℂ)) ∧
            Γ.windingIntegral (((l+u)/2 : ℝ) : ℂ) = 1 ∧
            hillHminusHighContourAction n r K a (l : ℂ) (u : ℂ) Γ = hillHminusGapBoundaryAction K a l u ∧
            ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusHighContourAction n r K a (l : ℂ) (u : ℂ) Γ-
              (((u-l : ℝ) : ℂ)^2)‖ ≤ (u-l)^2*epsilon := by
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
  refine ⟨K,hK,hJ,?_⟩
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
  have hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,a))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) := by
    intro z hz
    exact (hJ (z,a) ⟨hz,ha⟩).comp (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  have hmatch' : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r), z.im ≠ 0 →
      K (z,a) = (hillHminusContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^2 :=
    fun z hz him => hmatch (z,a) ⟨⟨ball_subset_closedBall hz,ha⟩,
      mem_hillHminusContinuationDomain_of_im_ne_zero a hareal z him⟩
  have htrace : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      squaredCosh (K (z,a)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant a z/2 :=
    fun z hz => hrel (z,a) ⟨ball_subset_closedBall hz,ha⟩
  refine ⟨l,u,hlu,hpair,?_,?_⟩
  · intro z hz him
    have hs : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ 0 < s*z.im := by
      rcases lt_or_gt_of_ne him with hneg | hpos
      · exact ⟨-1,Or.inr rfl,by linarith⟩
      · exact ⟨1,Or.inl rfl,by simpa using hpos⟩
    obtain ⟨s,hs,hside⟩ := hs
    have he := hillHminusOffGapPrimitive_eq_shifted_half_disc n r hr K a hareal l u hlu hpair hS
      (fun w hw => (hnorm w hw).trans_lt heta1) hf hmatch' s hs z hz hside
    exact ⟨he,hillHminusOffGapRoot_eq_continued n r K a (l : ℂ) (u : ℂ) z
      (mem_hillHminusContinuationDomain_of_im_ne_zero a hareal z him) he⟩
  · obtain ⟨Γ,hin,hw,he⟩ := exists_hillHminus_high_contour_action n r eta hr heta1 V K hJ
      a ha l u hlu hpair hf hnorm htrace
    obtain ⟨_,_,herror⟩ := hillHminusGapBoundaryAction_properties n r eta hr heta1 V K hJ
      a ha l u hlu hpair hf hnorm
    refine ⟨Γ,hin,hw,he,?_⟩
    rw [he]
    exact herror.trans (mul_le_mul_of_nonneg_left hetaε (sq_nonneg _))

end NLS.KdV
