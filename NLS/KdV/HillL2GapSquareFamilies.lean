import NLS.KdV.HillL2WholeGapSquares
import NLS.KdV.HillL2SmallGapCoverage

/-! # Complete actual high L2 gaps inside analytic square discs

One complex L2 neighborhood and one cutoff support the full high family.
Each actual two-root gap, including a collapsed pair, lies strictly
inside one disc carrying its actual analytic squared primitive.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

/-- The analytic energy discs contain the whole actual high gaps, with
one complex neighborhood and cutoff chosen before every pair. One square
per index covers both endpoints and the complete straight complex gap
segment, including a collapsed pair. No endpoint gluing is assumed. -/
theorem exists_hillL2_whole_gap_squares (q : Coeff 2) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (Coeff 2),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ K (hillL2GapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V, ‖K t‖ < 1) ∧
        (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillL2Discriminant t.2 t.1/2) ∧
        (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
          K t = 0 ↔ hillL2Radicand t.2 t.1 = 0) ∧
        (∀ t ∈ (hillL2GapSquareDisc n r ×ˢ V) ∩ hillL2ContinuationDomain,
          K t = (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        ∀ a ∈ V, ∃ l u : ℂ, HillL2HighGapPair a n l u ∧
          segment ℝ l u ⊆ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by
  obtain ⟨r,Nk,Vk,hr,hrpi,hNk,hVk,hqk,hfamily⟩ := exists_hillL2_whole_disc_squares q
  obtain ⟨Nr,Vr,_,hVr,hqr,hcover⟩ := exists_hillL2_small_gap_coverage q (r/4)
    (by positivity) (by linarith)
  obtain ⟨Nc,Vc,_,hVc,hqc,hcount⟩ := exists_hillL2Counting_near_compact {q} isCompact_singleton
  let N := max Nk (max Nr (Nc+1))
  let V := Vk ∩ (Vr ∩ Vc)
  have hqV : q ∈ V := ⟨hqk,hqr,hqc (mem_singleton q)⟩
  refine ⟨r,N,V,hr,hrpi,hNk.trans_le (le_max_left _ _),hVk.inter (hVr.inter hVc),hqV,?_⟩
  intro n hn
  have hnk : Nk ≤ (n : ℕ) := (le_max_left Nk _).trans hn
  have hnr : Nr ≤ (n : ℕ) := (le_max_left Nr _).trans ((le_max_right Nk _).trans hn)
  have hnc : Nc < (n : ℕ) := by dsimp only [N] at hn; omega
  obtain ⟨K,hK,hbound,hrel,hzero,hmatch⟩ := hfamily n hnk
  have hsub : hillL2GapSquareDisc n r ×ˢ V ⊆ hillL2GapSquareDisc n r ×ˢ Vk :=
    fun _ ht => ⟨ht.1,ht.2.1⟩
  refine ⟨K,hK.mono hsub,fun t ht => hbound t (hsub ht),fun t ht => hrel t (hsub ht),
    fun t ht => hzero t (hsub ht),fun t ht => hmatch t ⟨hsub ht.1,ht.2⟩,?_⟩
  intro a ha
  obtain ⟨l,u,hpair⟩ := exists_hillL2HighGapPair_of_counting a Nc
    (hcount a ha.2.2 Nc le_rfl) n hnc
  have hrc : r ≤ Real.pi*(n : ℕ) := by
    have hnreal : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
    nlinarith [Real.pi_pos]
  have endpoint_mem (lambda : ℂ) (hlambda : lambda ∈ hillL2HighEnergyRegion n)
      (hz : hillL2Radicand a lambda = 0) :
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

/-- Analytic symmetric pair data and actual unordered root pairs share
one complex L2 neighborhood and cutoff; individual labels are not chosen. -/
theorem exists_analytic_hillL2HighGapFamilies (q : Coeff 2) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) →
        AnalyticOnNhd ℂ (fun a => hillL2HighMidpoint a n) V ∧
        AnalyticOnNhd ℂ (fun a => hillL2HighSquaredGap a n) V ∧
        ∀ a ∈ V, ∃ l u : ℂ, HillL2HighGapPair a n l u := by
  obtain ⟨N,V,_,hV,hq,hcount⟩ := exists_hillL2Counting_near_compact {q} isCompact_singleton
  refine ⟨N+1,V,by omega,hV,hq (mem_singleton q),?_⟩
  intro n hn
  have hNn : N < (n : ℕ) := by omega
  refine ⟨?_,?_,?_⟩
  · intro a ha
    exact (analyticAt_hillL2High_symmetric a N (hcount a ha N le_rfl) n hNn).1
  · intro a ha
    exact (analyticAt_hillL2High_symmetric a N (hcount a ha N le_rfl) n hNn).2
  · intro a ha
    exact exists_hillL2HighGapPair_of_counting a N (hcount a ha N le_rfl) n hNn

/-- The same complex-neighborhood construction supplies ordered actual
real high pairs for real period-one L2 inputs, including collapsed gaps. -/
theorem exists_ordered_hillL2HighGapFamilies (q : Coeff 2) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a : WeightedCoeff SpectralWeight.one.toWeight 2,
        SpectralWeight.one.toCoeff a ∈ V →
        SpectralWeight.one.toCoeff a ∈ Coeff.paritySubspace 0 →
        IsRealHillPotential (SpectralWeight.one.toCoeff a) →
        ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ l u : ℂ,
          HillL2HighGapPair (SpectralWeight.one.toCoeff a) n l u ∧
            l.im = 0 ∧ u.im = 0 ∧ l.re ≤ u.re := by
  obtain ⟨N,V,hN,hV,hq,hfamily⟩ := exists_analytic_hillL2HighGapFamilies q
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro a ha hparity hreal n hn
  obtain ⟨l,u,hpair⟩ := (hfamily n hn).2.2 _ ha
  obtain ⟨hl,hu⟩ := hpair.im_eq_zero a hparity hreal
  by_cases he : l.re ≤ u.re
  · exact ⟨l,u,hpair,hl,hu,he⟩
  · exact ⟨u,l,hpair.swap,hu,hl,le_of_lt (lt_of_not_ge he)⟩

end NLS.KdV
