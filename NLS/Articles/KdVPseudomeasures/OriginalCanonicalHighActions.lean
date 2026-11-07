import NLS.Articles.KdVPseudomeasures.OriginalCanonicalActions
import NLS.Articles.KdVPseudomeasures.OriginalHighHillActions
import NLS.KdV.HillHminusOneNormalizedCanonicalDomain

/-! # Original canonical actions inherit the exact high-frequency normalization

The same original Hill indices are identified before comparison. One
complex neighborhood and cutoff work for ALL original real inputs there
and every higher index. A common connected complex domain also supports
locally uniform analytic ratio extensions around EVERY complex point.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

theorem exists_originalCanonicalHillAction_high_comparison (q : OriginalHminusOnePotential) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen V ∧ originalPeriodOneCoefficients q ∈ V ∧
      ∀ p : OriginalHminusOnePotential, originalPeriodOneCoefficients p ∈ V →
        ∀ n : ℕ+, N ≤ (n : ℕ) → originalCanonicalHillAction n p = originalHighHillAction n p ∧
          hillHminusGluedHighGapSquare n (originalPeriodOneCoefficients p) = originalCanonicalGapValues p (n : ℕ)^2 := by
  obtain ⟨N,V,hN,hV,_,hqV,_,hcomp⟩ := exists_hillHminus_uniform_canonical_high_comparison
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) 1 (by norm_num)
  refine ⟨N,V,hN,hV,hqV,?_⟩
  intro p hp n hn
  obtain ⟨_,heq,_,hgaps⟩ := hcomp n hn
  refine ⟨heq hp,?_⟩
  have hg := hgaps (originalPeriodOneCoefficients p) hp (originalPeriodOneCoefficients_real p)
  have hn0 : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  simpa only [originalCanonicalGapValues,if_neg hn0,Int.natAbs_natCast,originalHillLabels,ofReal_sub] using hg

theorem exists_originalCanonicalHillAction_high_normalization
    (q : OriginalHminusOnePotential) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen V ∧ originalPeriodOneCoefficients q ∈ V ∧
      ∀ p : OriginalHminusOnePotential, originalPeriodOneCoefficients p ∈ V → ∀ n : ℕ+, N ≤ (n : ℕ) →
        ‖originalHighHillActionRatio n p-1‖ ≤ epsilon ∧ originalHighHillActionRatio n p ≠ 0 ∧
        originalCanonicalHillAction n p = originalCanonicalGapValues p (n : ℕ)^2 /
          (8*((Real.pi : ℂ)*(n : ℕ)))*originalHighHillActionRatio n p ∧
        (originalCanonicalHillAction n p = 0 ↔ originalCanonicalGapValues p (n : ℕ) = 0) ∧
        ‖(8*((Real.pi : ℂ)*(n : ℕ)))*originalCanonicalHillAction n p-originalCanonicalGapValues p (n : ℕ)^2‖ ≤
          ‖originalCanonicalGapValues p (n : ℕ)‖^2*epsilon := by
  obtain ⟨N,V,hN,hV,hqV,_,hdata⟩ := exists_hillHminus_uniform_canonical_high_normalization
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) epsilon hepsilon
  refine ⟨N,V,hN,hV,hqV,?_⟩
  intro p hp n hn
  have hd := hdata n hn
  have hg := hd.2.2.2 (originalPeriodOneCoefficients p) hp (originalPeriodOneCoefficients_real p)
  have hn0 : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hg' : hillHminusGluedHighGapSquare n (originalPeriodOneCoefficients p) = originalCanonicalGapValues p (n : ℕ)^2 := by
    simpa only [originalCanonicalGapValues,if_neg hn0,Int.natAbs_natCast,originalHillLabels,ofReal_sub] using hg
  obtain ⟨hclose,hnz,hfactor,hzero,herror⟩ := hd.2.2.1 (originalPeriodOneCoefficients p) hp
  rw [hg'] at hfactor hzero herror
  rw [sq_eq_zero_iff] at hzero
  rw [norm_pow] at herror
  exact ⟨hclose,hnz,hfactor,hzero,herror⟩

theorem exists_common_normalized_complex_neighborhood_originalCanonicalHillActions :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ IsConnected W ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ W) ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalAction n) W) ∧
      ∀ a ∈ W, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen U ∧ a ∈ U ∧ U ⊆ W ∧
          ∀ n : ℕ+, N ≤ (n : ℕ) → AnalyticOnNhd ℂ (hillHminusGluedHighActionRatio n) U ∧
            ∀ b ∈ U, ‖hillHminusGluedHighActionRatio n b-1‖ ≤ epsilon ∧
              hillHminusGluedHighActionRatio n b ≠ 0 ∧
              ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalAction n b-hillHminusGluedHighGapSquare n b‖ ≤
                ‖hillHminusGluedHighGapSquare n b‖*epsilon := by
  refine ⟨hillHminusNormalizedCanonicalActionDomain,isOpen_hillHminusNormalizedCanonicalActionDomain,
    isConnected_hillHminusNormalizedCanonicalActionDomain,
    (fun q => real_mem_hillHminusNormalizedCanonicalActionDomain _ (originalPeriodOneCoefficients_real q)),
    analyticOnNhd_hillHminusCanonicalAction_on_normalizedDomain,?_⟩
  intro a ha epsilon hepsilon
  obtain ⟨N,U,hN,hU,haU,hUW,hdata⟩ := exists_hillHminus_canonical_high_normalization_at_complex a ha epsilon hepsilon
  refine ⟨N,U,hN,hU,haU,hUW,?_⟩
  intro n hn
  have hd := hdata n hn
  refine ⟨hd.1,?_⟩
  intro b hb
  obtain ⟨hclose,hnz,_,_,herror⟩ := hd.2.2.1 b hb
  exact ⟨hclose,hnz,herror⟩

end NLS.Articles.KdVPseudomeasures
