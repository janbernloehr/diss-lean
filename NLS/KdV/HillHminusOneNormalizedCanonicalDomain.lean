import NLS.KdV.HillHminusOneUniformCanonicalHighActions

/-! # A common complex domain with locally uniform canonical high normalization

Each proved neighborhood contains a real anchor and has one cutoff
before the entire correctly indexed high comparison. Their union is open
and connected and contains the full real form. At EVERY COMPLEX point
of this domain, the existing complex high estimates transfer locally to
the canonical family, with one neighborhood and cutoff before all indices.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

structure HillHminusCanonicalHighNeighborhood where
  source : Set PeriodOneHminusOne
  source_open : IsOpen source
  source_preconnected : IsPreconnected source
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  center_mem : center ∈ source
  subset_canonical : source ⊆ hillHminusCanonicalActionDomain
  cutoff : ℕ
  cutoff_ge_two : 2 ≤ cutoff
  comparison : ∀ n : ℕ+, cutoff ≤ (n : ℕ) → source ⊆ hillHminusHighActionDomain n ∧
    EqOn (hillHminusCanonicalAction n) (hillHminusGluedHighAction n) source
  real_gap : ∀ n : ℕ+, cutoff ≤ (n : ℕ) → ∀ a ∈ source, ∀ ha : IsRealPeriodOneHminusOne a,
    hillHminusGluedHighGapSquare n a =
      ((hillHminusLabels a ha (2*(n : ℕ)) : ℂ)-(hillHminusLabels a ha (2*(n : ℕ)-1) : ℂ))^2

theorem HillHminusCanonicalHighNeighborhood.canonical_gap_factorization
    (B : HillHminusCanonicalHighNeighborhood) (n : ℕ+) (hn : B.cutoff ≤ (n : ℕ))
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    hillHminusCanonicalAction n q = hillHminusGluedHighGapSquare n q /
      (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusGluedHighActionRatio n q := by
  rw [(B.comparison n hn).2 hq]
  rfl

theorem HillHminusCanonicalHighNeighborhood.canonical_normalized_quotient
    (B : HillHminusCanonicalHighNeighborhood) (n : ℕ+) (hn : B.cutoff ≤ (n : ℕ))
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hg : hillHminusGluedHighGapSquare n q ≠ 0) :
    (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalAction n q/hillHminusGluedHighGapSquare n q =
      hillHminusGluedHighActionRatio n q := by
  rw [(B.comparison n hn).2 hq]
  exact hillHminusGluedHighAction_normalized_quotient n q hg

theorem exists_hillHminusCanonicalHighNeighborhood
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ B : HillHminusCanonicalHighNeighborhood, q ∈ B.source := by
  obtain ⟨N,W,hN,hW,hconn,hqW,hsub,hcomp⟩ :=
    exists_hillHminus_uniform_canonical_high_comparison q hq 1 (by norm_num)
  let B : HillHminusCanonicalHighNeighborhood := {
    source := W
    source_open := hW
    source_preconnected := hconn
    center := q
    center_real := hq
    center_mem := hqW
    subset_canonical := hsub
    cutoff := N
    cutoff_ge_two := hN
    comparison := fun n hn => ⟨(hcomp n hn).1,(hcomp n hn).2.1⟩
    real_gap := fun n hn => (hcomp n hn).2.2.2 }
  exact ⟨B,hqW⟩

def hillHminusNormalizedCanonicalActionDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillHminusCanonicalHighNeighborhood, B.source

theorem isOpen_hillHminusNormalizedCanonicalActionDomain :
    IsOpen hillHminusNormalizedCanonicalActionDomain := isOpen_iUnion (fun B => B.source_open)

theorem hillHminusNormalizedCanonicalActionDomain_subset :
    hillHminusNormalizedCanonicalActionDomain ⊆ hillHminusCanonicalActionDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.subset_canonical hB

theorem real_mem_hillHminusNormalizedCanonicalActionDomain
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    q ∈ hillHminusNormalizedCanonicalActionDomain := by
  obtain ⟨B,hB⟩ := exists_hillHminusCanonicalHighNeighborhood q hq
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem isConnected_hillHminusNormalizedCanonicalActionDomain :
    IsConnected hillHminusNormalizedCanonicalActionDomain := by
  let R : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hR : IsPreconnected R := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillHminusCanonicalHighNeighborhood) : IsPreconnected (R ∪ B.source) :=
    hR.union B.center B.center_real B.center_mem B.source_preconnected
  have hcommon : (⋂ B : HillHminusCanonicalHighNeighborhood, R ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillHminusCanonicalHighNeighborhood, R ∪ B.source) =
      hillHminusNormalizedCanonicalActionDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqR | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusNormalizedCanonicalActionDomain q hqR
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusNormalizedCanonicalActionDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

theorem analyticOnNhd_hillHminusCanonicalAction_on_normalizedDomain (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalAction n) hillHminusNormalizedCanonicalActionDomain :=
  (analyticOnNhd_hillHminusCanonicalAction n).mono hillHminusNormalizedCanonicalActionDomain_subset

theorem exists_hillHminus_canonical_high_normalization_at_complex
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusNormalizedCanonicalActionDomain)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ W : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen W ∧ q ∈ W ∧
      W ⊆ hillHminusNormalizedCanonicalActionDomain ∧
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
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  obtain ⟨L,V,_,hV,hqV,hest⟩ := exists_hillHminus_uniform_glued_high_actions q epsilon hepsilon
  let W := B.source ∩ V
  have hWnorm : W ⊆ hillHminusNormalizedCanonicalActionDomain := fun a ha => mem_iUnion.mpr ⟨B,ha.1⟩
  refine ⟨max B.cutoff L,W,B.cutoff_ge_two.trans (le_max_left _ _),B.source_open.inter hV,
    ⟨hB,hqV⟩,hWnorm,?_⟩
  intro n hn
  have hnB : B.cutoff ≤ (n : ℕ) := (le_max_left _ _).trans hn
  have hnL : L ≤ (n : ℕ) := (le_max_right _ _).trans hn
  have hdom : W ⊆ hillHminusHighActionDomain n := fun a ha => (B.comparison n hnB).1 ha.1
  refine ⟨(analyticOnNhd_hillHminusGluedHighActionRatio n).mono hdom,
    (analyticOnNhd_hillHminusGluedHighGapSquare n).mono hdom,?_,?_⟩
  · intro a ha
    obtain ⟨hb,hnz,hzero,herror⟩ := (hest n hnL).2 a ha.2
    rw [(B.comparison n hnB).2 ha.1]
    exact ⟨hb,hnz,rfl,hzero,herror⟩
  · intro a ha har
    exact B.real_gap n hnB a ha.1 har

end NLS.KdV
