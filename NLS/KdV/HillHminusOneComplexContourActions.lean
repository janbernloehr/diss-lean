import NLS.KdV.HillHminusOneContourActionPeriod

/-! # Uniform native high contour actions for complex H-minus-one potentials

Actual enclosing circles exist for every complex or collapsed high pair.
One open complex neighborhood and cutoff work simultaneously for all
later indices and all complex inputs. The normalization estimate and
contour independence apply to every admissible winding-one contour.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem HillHminusHighGapPair.exists_winding_one_contour
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℂ}
    (hpair : HillHminusHighGapPair q n r l u) :
    ∃ Γ : PiecewiseC1Loop,
      Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u) ∧
      Γ.windingIntegral ((l+u)/2) = 1 := by
  have hseg : standardRootGapSegment ((l+u)/2) ((u-l)/2) = segment ℝ l u := by
    rw [standardRootGapSegment_eq_segment]
    congr 1 <;> ring
  have hgap : standardRootGapSegment ((l+u)/2) ((u-l)/2) ⊆
      ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by
    rw [hseg]
    exact (convex_ball _ _).segment_subset hpair.left_mem hpair.right_mem
  obtain ⟨Γ,hin,hw⟩ := exists_endpointGap_winding_one_contour _ _ _ _ hgap
  exact ⟨Γ,by rwa [hseg] at hin,hw⟩

theorem exists_hillHminus_uniform_complex_contour_actions (q : PeriodOneHminusOne) :
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
        ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
          ∃ Γ₀ : PiecewiseC1Loop,
            Γ₀.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u) ∧
            Γ₀.windingIntegral ((l+u)/2) = 1 ∧
            ∀ Γ : PiecewiseC1Loop,
              Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u) →
              Γ.windingIntegral ((l+u)/2) = 1 →
              hillHminusHighContourAction n r K a l u Γ = hillHminusHighContourAction n r K a l u Γ₀ ∧
              ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusHighContourAction n r K a l u Γ-(u-l)^2‖ ≤
                ‖u-l‖^2*epsilon := by
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
  refine ⟨K,hK,hrel,hmatch,hJ,?_⟩
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
  obtain ⟨Γ₀,hin,hw⟩ := hpair.exists_winding_one_contour
  refine ⟨l,u,hpair,Γ₀,hin,hw,?_⟩
  intro Γ hΓ hΓw
  refine ⟨hillHminusHighContourAction_eq_of_winding_eq n r hr K a l u hpair hS hf htrace
    Γ Γ₀ hΓ hin (hΓw.trans hw.symm),?_⟩
  exact (norm_hillHminusHighContourAction_error_le n r eta hr K a l u hpair hS hf htrace hnorm Γ hΓ hΓw).trans
    (mul_le_mul_of_nonneg_left hetaε (sq_nonneg _))

end NLS.KdV
