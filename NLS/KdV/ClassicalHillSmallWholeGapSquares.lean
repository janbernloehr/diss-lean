import NLS.KdV.ClassicalHillWholeGapSquares

noncomputable section
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV
theorem exists_classicalHill_whole_gap_small_squares (q : Curve ℂ) (B : ℝ) (hB : 0 < B) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (Curve ℂ),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Curve ℂ → ℂ,
        AnalyticOnNhd ℂ K (classicalHillGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V, ‖K t‖ < B) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*classicalHillDiscriminant t.2 t.1/2) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V,
          K t = 0 ↔ classicalHillRadicand t = 0) ∧
        (∀ t ∈ (classicalHillGapSquareDisc n r ×ˢ V) ∩ classicalHillContinuationDomain,
          K t = (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        ∀ a ∈ V, ∃ l u : ℂ, ClassicalHillHighGapPair a n l u ∧
          segment ℝ l u ⊆ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by
  obtain ⟨r,Nk,Vk,hr,hrpi,hNk,hVk,hqk,hfamily⟩ := exists_classicalHill_whole_disc_small_squares q B hB
  obtain ⟨Nr,Vr,_,hVr,hqr,hcover⟩ := exists_classicalHill_small_gap_coverage q (r/4)
    (by positivity) (by linarith)
  obtain ⟨Nc,Vc,_,hVc,hqc,hcount⟩ := exists_classicalHillCounting_near_compact {q} isCompact_singleton
  let N := max Nk (max Nr (Nc+1))
  let V := Vk ∩ (Vr ∩ Vc)
  have hqV : q ∈ V := ⟨hqk,hqr,hqc (mem_singleton q)⟩
  refine ⟨r,N,V,hr,hrpi,hNk.trans_le (le_max_left _ _),hVk.inter (hVr.inter hVc),hqV,?_⟩
  intro n hn
  have hnk : Nk ≤ (n : ℕ) := (le_max_left Nk _).trans hn
  have hnr : Nr ≤ (n : ℕ) := (le_max_left Nr _).trans ((le_max_right Nk _).trans hn)
  have hnc : Nc < (n : ℕ) := by dsimp only [N] at hn; omega
  obtain ⟨K,hK,hbound,hrel,hzero,hmatch⟩ := hfamily n hnk
  have hsub : classicalHillGapSquareDisc n r ×ˢ V ⊆ classicalHillGapSquareDisc n r ×ˢ Vk :=
    fun _ ht => ⟨ht.1,ht.2.1⟩
  refine ⟨K,hK.mono hsub,fun t ht => hbound t (hsub ht),fun t ht => hrel t (hsub ht),
    fun t ht => hzero t (hsub ht),fun t ht => hmatch t ⟨hsub ht.1,ht.2⟩,?_⟩
  intro a ha
  obtain ⟨l,u,hpair⟩ := exists_classicalHillHighGapPair_of_counting a Nc
    (hcount a ha.2.2 Nc le_rfl) n hnc
  have hrc : r ≤ Real.pi*(n : ℕ) := by
    have hnreal : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
    nlinarith [Real.pi_pos]
  have endpoint_mem (lambda : ℂ) (hlambda : lambda ∈ classicalHillHighEnergyRegion n)
      (hz : classicalHillRadicand (lambda,a) = 0) :
      lambda ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by
    obtain ⟨z,hzball,hzsq⟩ := hlambda
    change z^2 = lambda at hzsq
    have hsmall := hcover a ha.2.1 (n : ℕ) (by simpa only [Int.natAbs_natCast] using hnr) z
      (by simpa only [Int.cast_natCast] using ball_subset_closedBall hzball)
      (by simpa only [hzsq] using hz)
    have h := square_mem_energy_ball_of_small_frequency (Real.pi*(n : ℕ)) r (by positivity) hr hrc z
      (by simpa only [ofReal_mul,ofReal_natCast,Int.cast_natCast] using hsmall)
    simpa only [hzsq,ofReal_mul,ofReal_natCast] using h
  refine ⟨l,u,hpair,?_⟩
  exact (convex_ball _ _).segment_subset
    (endpoint_mem l hpair.left_mem hpair.left_zero) (endpoint_mem u hpair.right_mem hpair.right_zero)


end NLS.KdV
