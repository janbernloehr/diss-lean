import NLS.KdV.HillHminusOneCanonicalHighComparison
import NLS.KdV.HillHminusOneUniformCanonicalPairs
import NLS.KdV.HillHminusOneUniformGluedActions

/-! # Uniform complex comparison and normalization of the canonical high actions

One complex ball and cutoff precede ALL later indices. The full original
label construction identifies the high pair for EVERY real input there.
Physical real-form uniqueness extends the action equality to the WHOLE
complex ball, retaining the previously proved analytic ratio and exact
8*pi*n normalization. No claim is made on unrelated old chart components.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

theorem exists_hillHminus_uniform_canonical_high_comparison
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ W : Set PeriodOneHminusOne,
      2 ≤ N ∧ IsOpen W ∧ IsPreconnected W ∧ q ∈ W ∧ W ⊆ hillHminusCanonicalActionDomain ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) →
        W ⊆ hillHminusHighActionDomain n ∧
        EqOn (hillHminusCanonicalAction n) (hillHminusGluedHighAction n) W ∧
        (∀ a ∈ W, ‖hillHminusGluedHighActionRatio n a-1‖ ≤ epsilon ∧
          hillHminusGluedHighActionRatio n a ≠ 0) ∧
        ∀ a ∈ W, ∀ ha : IsRealPeriodOneHminusOne a,
          hillHminusGluedHighGapSquare n a =
            ((hillHminusLabels a ha (2*(n : ℕ)) : ℂ)-(hillHminusLabels a ha (2*(n : ℕ)-1) : ℂ))^2 := by
  obtain ⟨s,M,U,_,_,hM,hU,hqU,hpairs⟩ := exists_hillHminus_uniform_canonical_label_pairs q
  obtain ⟨r,_,_,hfamily⟩ := exists_hillHminus_uniform_action_neighborhoods q
  obtain ⟨L,V,_,hV,hqV,hfamily⟩ := hfamily epsilon hepsilon
  let O : Set PeriodOneHminusOne := U ∩ (V ∩ hillHminusCanonicalActionDomain)
  have hO : IsOpen O := hU.inter (hV.inter isOpen_hillHminusCanonicalActionDomain)
  have hqO : q ∈ O := ⟨hqU,hqV,real_mem_hillHminusCanonicalActionDomain q hq⟩
  obtain ⟨rho,hrho,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hqO)
  let W : Set PeriodOneHminusOne := ball q rho
  have hqW : q ∈ W := mem_ball_self hrho
  have hWcanon : W ⊆ hillHminusCanonicalActionDomain := fun a ha => (hball ha).2.2
  refine ⟨max M L,W,hM.trans (le_max_left _ _),isOpen_ball,(convex_ball q rho).isPreconnected,hqW,hWcanon,?_⟩
  intro n hn
  have hnM : M ≤ (n : ℕ) := (le_max_left _ _).trans hn
  have hnL : L ≤ (n : ℕ) := (le_max_right _ _).trans hn
  obtain ⟨K,hK,hR⟩ := hfamily n hnL
  have hWold : W ⊆ hillHminusHighActionDomain n := fun a ha => hK.mem_highActionDomain (hball ha).2.1
  have hpair (a : PeriodOneHminusOne) (ha : a ∈ W) (har : IsRealPeriodOneHminusOne a) :
      HillHminusHighGapPair a n r (hillHminusLabels a har (2*(n : ℕ)-1) : ℂ)
        (hillHminusLabels a har (2*(n : ℕ)) : ℂ) := by
    have hp := hpairs a (hball ha).1 har n hnM
    obtain ⟨l,u,hp'⟩ := (hK.valid (hball ha).2.1).2.2.2.2.2.2
    exact hp.align_other_radius hp'
  have hreal (a : PeriodOneHminusOne) (ha : a ∈ W) (har : IsRealPeriodOneHminusOne a) :
      hillHminusCanonicalAction n a = hillHminusGluedHighAction n a :=
    (hK.glued_action_eq_canonical_of_real_labels a (hball ha).2.1 har
      (hillHminusLabels a har (2*(n : ℕ)-1)) (hillHminusLabels a har (2*(n : ℕ)))
      (hpair a ha har) rfl rfl).symm
  have heq : EqOn (hillHminusCanonicalAction n) (hillHminusGluedHighAction n) W :=
    analytic_eqOn_of_real_periodOneHminus W isOpen_ball (convex_ball q rho).isPreconnected
      ⟨q,hqW,hq⟩ _ _ ((analyticOnNhd_hillHminusCanonicalAction n).mono hWcanon)
      ((analyticOnNhd_hillHminusGluedHighAction n).mono hWold) hreal
  refine ⟨hWold,heq,?_,?_⟩
  · intro a ha
    rw [hK.glued_ratio_eq (hball ha).2.1]
    exact hR a (hball ha).2.1
  · intro a ha har
    exact hK.glued_gap_square_eq_pair (hball ha).2.1 _ _ (hpair a ha har)

theorem exists_hillHminus_uniform_canonical_high_normalization
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ W : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen W ∧ q ∈ W ∧
      W ⊆ hillHminusCanonicalActionDomain ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) →
        AnalyticOnNhd ℂ (hillHminusGluedHighActionRatio n) W ∧
        AnalyticOnNhd ℂ (hillHminusGluedHighGapSquare n) W ∧
        (∀ a ∈ W, ‖hillHminusGluedHighActionRatio n a-1‖ ≤ epsilon ∧
          hillHminusGluedHighActionRatio n a ≠ 0 ∧
          hillHminusCanonicalAction n a = hillHminusGluedHighGapSquare n a /
            (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusGluedHighActionRatio n a ∧
          (hillHminusCanonicalAction n a = 0 ↔ hillHminusGluedHighGapSquare n a = 0) ∧
          ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalAction n a-hillHminusGluedHighGapSquare n a‖ ≤
            ‖hillHminusGluedHighGapSquare n a‖*epsilon) ∧
        ∀ a ∈ W, ∀ ha : IsRealPeriodOneHminusOne a,
          hillHminusGluedHighGapSquare n a =
            ((hillHminusLabels a ha (2*(n : ℕ)) : ℂ)-(hillHminusLabels a ha (2*(n : ℕ)-1) : ℂ))^2 := by
  obtain ⟨N,W,hN,hW,_,hqW,hWcanon,hcomp⟩ :=
    exists_hillHminus_uniform_canonical_high_comparison q hq epsilon hepsilon
  refine ⟨N,W,hN,hW,hqW,hWcanon,?_⟩
  intro n hn
  obtain ⟨hdom,heq,hR,hgaps⟩ := hcomp n hn
  refine ⟨(analyticOnNhd_hillHminusGluedHighActionRatio n).mono hdom,
    (analyticOnNhd_hillHminusGluedHighGapSquare n).mono hdom,?_,hgaps⟩
  intro a ha
  obtain ⟨hb,hnz⟩ := hR a ha
  rw [heq ha]
  exact ⟨hb,hnz,rfl,hillHminusGluedHighAction_eq_zero_iff n a hnz,
    norm_hillHminusGluedHighAction_error_le n a epsilon hb⟩

end NLS.KdV
