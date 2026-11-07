import NLS.Articles.KdVPseudomeasures.OriginalCanonicalActions
import NLS.KdV.HillHminusOneCanonicalGapHighNormalization

/-! # Analytic squared gaps with the original physical Hill normalization

The common complex domain contains every original real mean-zero
period-one H-minus-one source. ALL original squared gaps and canonical
actions have analytic extensions on it, including the low indices and
collapsed gaps. High normalization is locally uniform at EVERY COMPLEX
point of this same domain. Low complex action quotients and Birkhoff
coordinates are separate, still necessary parts of source Theorem 3.2.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

theorem originalCanonicalGapSquare_eq (q : OriginalHminusOnePotential) (n : ℕ+) :
    hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) =
      originalCanonicalGapValues q (n : ℕ)^2 := by
  have hn : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  simpa only [originalCanonicalGapValues,if_neg hn,Int.natAbs_natCast,originalHillLabels,ofReal_sub]
    using hillHminusCanonicalGapSquare_eq_real (originalPeriodOneCoefficients q)
      (originalPeriodOneCoefficients_real q) n

theorem originalCanonicalHillAction_eq_zero_iff_gapSquare
    (q : OriginalHminusOnePotential) (n : ℕ+) :
    originalCanonicalHillAction n q = 0 ↔
      hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) = 0 :=
  hillHminusCanonicalAction_eq_zero_iff_gapSquare_of_real (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q) n

theorem exists_common_complex_neighborhood_originalCanonicalGapSquares :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ IsConnected W ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ W) ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalAction n) W ∧
        AnalyticOnNhd ℂ (hillHminusCanonicalGapSquare n) W ∧
        ∀ q : OriginalHminusOnePotential,
          hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) =
            originalCanonicalGapValues q (n : ℕ)^2 := by
  refine ⟨hillHminusCanonicalGapDomain,isOpen_hillHminusCanonicalGapDomain,
    isConnected_hillHminusCanonicalGapDomain,
    (fun q => real_mem_hillHminusCanonicalGapDomain _ (originalPeriodOneCoefficients_real q)),?_⟩
  intro n
  exact ⟨analyticOnNhd_hillHminusCanonicalAction_on_gapDomain n,
    analyticOnNhd_hillHminusCanonicalGapSquare n,fun q => originalCanonicalGapSquare_eq q n⟩

theorem exists_common_complex_neighborhood_originalCanonicalGap_high_normalization :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ IsConnected W ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ W) ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalAction n) W ∧
        AnalyticOnNhd ℂ (hillHminusCanonicalGapSquare n) W) ∧
      ∀ a ∈ W, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen U ∧ a ∈ U ∧ U ⊆ W ∧
          ∀ n : ℕ+, N ≤ (n : ℕ) → AnalyticOnNhd ℂ (hillHminusGluedHighActionRatio n) U ∧
            ∀ b ∈ U, ‖hillHminusGluedHighActionRatio n b-1‖ ≤ epsilon ∧
              hillHminusGluedHighActionRatio n b ≠ 0 ∧
              hillHminusCanonicalAction n b = hillHminusCanonicalGapSquare n b /
                (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusGluedHighActionRatio n b ∧
              (hillHminusCanonicalAction n b = 0 ↔ hillHminusCanonicalGapSquare n b = 0) ∧
              ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalAction n b-hillHminusCanonicalGapSquare n b‖ ≤
                ‖hillHminusCanonicalGapSquare n b‖*epsilon := by
  refine ⟨hillHminusCanonicalGapDomain,isOpen_hillHminusCanonicalGapDomain,
    isConnected_hillHminusCanonicalGapDomain,
    (fun q => real_mem_hillHminusCanonicalGapDomain _ (originalPeriodOneCoefficients_real q)),
    (fun n => ⟨analyticOnNhd_hillHminusCanonicalAction_on_gapDomain n,
      analyticOnNhd_hillHminusCanonicalGapSquare n⟩),?_⟩
  intro a ha epsilon hepsilon
  obtain ⟨N,U,hN,hU,haU,hUW,hdata⟩ :=
    exists_hillHminus_canonical_gap_high_normalization_at_complex a ha epsilon hepsilon
  refine ⟨N,U,hN,hU,haU,hUW,?_⟩
  intro n hn
  refine ⟨(hdata n hn).1,?_⟩
  intro b hb
  obtain ⟨hclose,hnz,hfactor,hzero,herror,_⟩ := (hdata n hn).2 b hb
  exact ⟨hclose,hnz,hfactor,hzero,herror⟩

end NLS.Articles.KdVPseudomeasures
