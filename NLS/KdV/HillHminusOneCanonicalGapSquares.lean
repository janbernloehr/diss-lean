import NLS.KdV.HillHminusOneMiuraGapBalls

/-! # Canonical squared Hill gaps on a common complex neighborhood

All local Miura formulas agree on entire complex overlaps. Their glued
functions are analytic at every positive index on ONE open connected
domain containing the full real H-minus-one form. Every valid local
formula gives the same value, independently of the lift and energy shift.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped Classical
namespace NLS.KdV

def hillHminusCanonicalGapDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillHminusMiuraGapBall, B.source

theorem isOpen_hillHminusCanonicalGapDomain : IsOpen hillHminusCanonicalGapDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem hillHminusCanonicalGapDomain_subset :
    hillHminusCanonicalGapDomain ⊆ hillHminusNormalizedCanonicalActionDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact mem_iUnion.mpr ⟨B.highNeighborhood,B.high_subset hB⟩

theorem real_mem_hillHminusCanonicalGapDomain (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : q ∈ hillHminusCanonicalGapDomain := by
  obtain ⟨B,hB⟩ := exists_hillHminusMiuraGapBall q hq
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem isConnected_hillHminusCanonicalGapDomain : IsConnected hillHminusCanonicalGapDomain := by
  let R : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hR : IsPreconnected R := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillHminusMiuraGapBall) : IsPreconnected (R ∪ B.source) :=
    hR.union B.actionBall.center B.actionBall.center_real (mem_ball_self B.actionBall.radius_pos)
      (convex_ball B.actionBall.center B.actionBall.radius).isPreconnected
  have hcommon : (⋂ B : HillHminusMiuraGapBall, R ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillHminusMiuraGapBall, R ∪ B.source) = hillHminusCanonicalGapDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqR | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusCanonicalGapDomain q hqR
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusCanonicalGapDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

def hillHminusCanonicalGapSquare (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  if hq : q ∈ hillHminusCanonicalGapDomain then
    (Classical.choose (mem_iUnion.mp hq)).gapSquare n q
  else 0

theorem HillHminusMiuraGapBall.canonical_gapSquare_eq (B : HillHminusMiuraGapBall)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    hillHminusCanonicalGapSquare n q = B.gapSquare n q := by
  have hdom : q ∈ hillHminusCanonicalGapDomain := mem_iUnion.mpr ⟨B,hq⟩
  rw [hillHminusCanonicalGapSquare,dif_pos hdom]
  let C : HillHminusMiuraGapBall := Classical.choose (mem_iUnion.mp hdom)
  have hC : q ∈ C.source := Classical.choose_spec (mem_iUnion.mp hdom)
  exact C.gapSquare_eq_on_overlap B n ⟨hC,hq⟩

theorem analyticOnNhd_hillHminusCanonicalGapSquare (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalGapSquare n) hillHminusCanonicalGapDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  apply (B.analytic_gapSquare n q hB).congr
  filter_upwards [B.source_open.mem_nhds hB] with a ha
  exact (B.canonical_gapSquare_eq n a ha).symm

theorem analyticOnNhd_hillHminusCanonicalAction_on_gapDomain (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalAction n) hillHminusCanonicalGapDomain :=
  (analyticOnNhd_hillHminusCanonicalAction_on_normalizedDomain n).mono hillHminusCanonicalGapDomain_subset

theorem hillHminusCanonicalGapSquare_eq_real (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusCanonicalGapSquare n q =
      ((hillHminusLabels q hq (2*(n : ℕ)) : ℂ)-(hillHminusLabels q hq (2*(n : ℕ)-1) : ℂ))^2 := by
  obtain ⟨B,hB⟩ := exists_hillHminusMiuraGapBall q hq
  exact (B.canonical_gapSquare_eq n q hB).trans (B.gapSquare_eq_real n q hB hq)

theorem hillHminusCanonicalGapSquare_eq_Miura_of_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (n : ℕ+) :
    hillHminusCanonicalGapSquare n q =
      ((hillMiuraDiracRight u.val (n : ℕ)-hillMiuraDiracLeft u.val (n : ℕ))*
        (hillMiuraDiracRight u.val (n : ℕ)+hillMiuraDiracLeft u.val (n : ℕ)))^2 := by
  rw [hillHminusCanonicalGapSquare_eq_real q hq n,← ofReal_sub,
    hillHminus_gap_eq_miuraDirac_product q hq u c himage hc (n : ℕ) n.pos]

theorem hillHminusCanonicalAction_eq_zero_iff_gapSquare_of_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusCanonicalAction n q = 0 ↔ hillHminusCanonicalGapSquare n q = 0 := by
  rw [hillHminusCanonicalGapSquare_eq_real,sq_eq_zero_iff,← ofReal_sub]
  exact (hillHminusCanonicalAction_real_properties q hq n).2.2

end NLS.KdV
