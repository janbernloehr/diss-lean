import NLS.KdV.HillHminusOneCanonicalGapSquares

/-! # Locally uniform high normalization for the glued canonical gap squares

Each real-centered Miura ball retains its verified original-index high
comparison. Physical real-form uniqueness therefore identifies the new
all-index gap square with the previous high gap square throughout that
complex ball. At EVERY complex point of the common gap domain, one
neighborhood and cutoff precede all high ratio estimates and identities.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

theorem HillHminusMiuraGapBall.canonical_gapSquare_eq_high
    (B : HillHminusMiuraGapBall) (n : ℕ+) (hn : B.highNeighborhood.cutoff ≤ (n : ℕ)) :
    EqOn (hillHminusCanonicalGapSquare n) (hillHminusGluedHighGapSquare n) B.source := by
  have hdom : B.source ⊆ hillHminusHighActionDomain n :=
    fun a ha => (B.highNeighborhood.comparison n hn).1 (B.high_subset ha)
  have hgap : B.source ⊆ hillHminusCanonicalGapDomain := fun a ha => mem_iUnion.mpr ⟨B,ha⟩
  apply analytic_eqOn_of_real_periodOneHminus B.source B.source_open
    (convex_ball B.actionBall.center B.actionBall.radius).isPreconnected
    ⟨B.actionBall.center,mem_ball_self B.actionBall.radius_pos,B.actionBall.center_real⟩
    _ _ ((analyticOnNhd_hillHminusCanonicalGapSquare n).mono hgap)
    ((analyticOnNhd_hillHminusGluedHighGapSquare n).mono hdom)
  intro a ha har
  exact (hillHminusCanonicalGapSquare_eq_real a har n).trans
    (B.highNeighborhood.real_gap n hn a (B.high_subset ha) har).symm

theorem exists_hillHminus_canonical_gap_high_normalization_at_complex
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalGapDomain)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen U ∧ q ∈ U ∧
      U ⊆ hillHminusCanonicalGapDomain ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) →
        AnalyticOnNhd ℂ (hillHminusGluedHighActionRatio n) U ∧
        ∀ a ∈ U, ‖hillHminusGluedHighActionRatio n a-1‖ ≤ epsilon ∧
          hillHminusGluedHighActionRatio n a ≠ 0 ∧
          hillHminusCanonicalAction n a = hillHminusCanonicalGapSquare n a /
            (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusGluedHighActionRatio n a ∧
          (hillHminusCanonicalAction n a = 0 ↔ hillHminusCanonicalGapSquare n a = 0) ∧
          ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalAction n a-hillHminusCanonicalGapSquare n a‖ ≤
            ‖hillHminusCanonicalGapSquare n a‖*epsilon ∧
          (hillHminusCanonicalGapSquare n a ≠ 0 →
            (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalAction n a/hillHminusCanonicalGapSquare n a =
              hillHminusGluedHighActionRatio n a) := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  obtain ⟨L,V,_,hV,hqV,hest⟩ := exists_hillHminus_uniform_glued_high_actions q epsilon hepsilon
  let U := B.source ∩ V
  refine ⟨max B.highNeighborhood.cutoff L,U,
    B.highNeighborhood.cutoff_ge_two.trans (le_max_left _ _),B.source_open.inter hV,
    ⟨hB,hqV⟩,(fun a ha => mem_iUnion.mpr ⟨B,ha.1⟩),?_⟩
  intro n hn
  have hnB : B.highNeighborhood.cutoff ≤ (n : ℕ) := (le_max_left _ _).trans hn
  have hnL : L ≤ (n : ℕ) := (le_max_right _ _).trans hn
  have hdom : U ⊆ hillHminusHighActionDomain n :=
    fun a ha => (B.highNeighborhood.comparison n hnB).1 (B.high_subset ha.1)
  refine ⟨(analyticOnNhd_hillHminusGluedHighActionRatio n).mono hdom,?_⟩
  intro a ha
  have hg := B.canonical_gapSquare_eq_high n hnB ha.1
  have hi := (B.highNeighborhood.comparison n hnB).2 (B.high_subset ha.1)
  obtain ⟨hclose,hnz,hzero,herror⟩ := (hest n hnL).2 a ha.2
  rw [hi,hg]
  refine ⟨hclose,hnz,rfl,hzero,herror,?_⟩
  exact hillHminusGluedHighAction_normalized_quotient n a

end NLS.KdV
