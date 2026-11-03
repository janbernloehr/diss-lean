import NLS.KdV.HillHminusOneMiuraActionBalls

/-! # Canonical Hill actions on one common complex H-minus-one neighborhood

The domain is the union of actual common Miura action balls. EVERY real
H-minus-one source belongs to it. Agreement on WHOLE complex overlaps
makes one chosen value agree with EVERY valid ball, at ALL positive
indices. The resulting functions are analytic on the SAME open domain
and equal the original real discriminant gap integral on its entire real
form. Values outside this domain are only a total-function convention.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusCanonicalActionDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillHminusMiuraActionBall, B.source

theorem isOpen_hillHminusCanonicalActionDomain : IsOpen hillHminusCanonicalActionDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem real_mem_hillHminusCanonicalActionDomain (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : q ∈ hillHminusCanonicalActionDomain := by
  obtain ⟨B,hB⟩ := exists_hillHminusMiuraActionBall q hq
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem isConnected_hillHminusCanonicalActionDomain : IsConnected hillHminusCanonicalActionDomain := by
  let R : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hR : IsPreconnected R := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillHminusMiuraActionBall) : IsPreconnected (R ∪ B.source) :=
    hR.union B.center B.center_real (mem_ball_self B.radius_pos) (convex_ball B.center B.radius).isPreconnected
  have hcommon : (⋂ B : HillHminusMiuraActionBall, R ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillHminusMiuraActionBall, R ∪ B.source) = hillHminusCanonicalActionDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqR | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusCanonicalActionDomain q hqR
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusCanonicalActionDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

def hillHminusCanonicalAction (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  if hq : q ∈ hillHminusCanonicalActionDomain then
    (Classical.choose (mem_iUnion.mp hq)).action n q
  else 0

theorem HillHminusMiuraActionBall.canonical_action_eq (B : HillHminusMiuraActionBall)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    hillHminusCanonicalAction n q = B.action n q := by
  have hdom : q ∈ hillHminusCanonicalActionDomain := mem_iUnion.mpr ⟨B,hq⟩
  rw [hillHminusCanonicalAction,dif_pos hdom]
  let C : HillHminusMiuraActionBall := Classical.choose (mem_iUnion.mp hdom)
  have hC : q ∈ C.source := Classical.choose_spec (mem_iUnion.mp hdom)
  exact C.action_eq_on_overlap B n ⟨hC,hq⟩

theorem analyticOnNhd_hillHminusCanonicalAction (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalAction n) hillHminusCanonicalActionDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  apply (B.analytic_action n q hB).congr
  filter_upwards [B.source_open.mem_nhds hB] with a ha
  exact (B.canonical_action_eq n a ha).symm

theorem hillHminusCanonicalAction_eq_real (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusCanonicalAction n q = hillHminusCanonicalRealAction q hq n := by
  obtain ⟨B,hB⟩ := exists_hillHminusMiuraActionBall q hq
  exact (B.canonical_action_eq n q hB).trans (B.action_eq_canonical_real n q hB hq)

theorem hillHminusCanonicalAction_eq_Miura_of_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (n : ℕ+) :
    hillHminusCanonicalAction n q = hillHminusMiuraIndexedAction u.val (n : ℕ) :=
  (hillHminusCanonicalAction_eq_real q hq n).trans
    (hillHminusMiuraIndexedAction_eq_canonicalRealAction q hq u c himage hc n).symm

theorem hillHminusCanonicalAction_real_properties
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    0 ≤ (hillHminusCanonicalAction n q).re ∧ (hillHminusCanonicalAction n q).im = 0 ∧
      (hillHminusCanonicalAction n q = 0 ↔
        ((hillHminusLabels q hq (2*(n : ℕ))-hillHminusLabels q hq (2*(n : ℕ)-1) : ℝ) : ℂ) = 0) := by
  rw [hillHminusCanonicalAction_eq_real q hq n]
  exact hillHminusCanonicalRealAction_properties q hq n

theorem exists_hillHminusCanonicalAction_Miura_contour
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    ∃ c : ℝ, ∃ u : PeriodOneRealL2,
      ∃ C : NLS.ZakharovShabat.SourceCriticalRootPeriodCircle (by simp) (by norm_num)
        (hillMiuraDiagonal u.val) (n : ℕ),
      periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)) ∧
      -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal q) ∧ 0 < C.center-C.radius ∧
      hillHminusCanonicalAction n q = hillHminusMiuraContourAction q u.val (c : ℂ)
        (NLS.ComplexAnalysis.quadraticEnergyLoop
          (NLS.ComplexAnalysis.PiecewiseC1Loop.circle (C.center : ℂ) C.radius) (c : ℂ)) ∧
      (NLS.ComplexAnalysis.quadraticEnergyLoop
        (NLS.ComplexAnalysis.PiecewiseC1Loop.circle (C.center : ℂ) C.radius) (c : ℂ)).windingIntegral
        ((NLS.ZakharovShabat.sourceStandardRootMidpoint (by simp) (by norm_num)
          (hillMiuraDiagonal u.val) (n : ℕ))^2-(c : ℂ)) = 1 := by
  obtain ⟨d,_,_,u,himage,houtside⟩ := exists_real_periodOneMiura_shift_outside_spectrum q hq 0
  have hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 ((d^2 : ℝ) : ℂ)) := by
    simpa only [ofReal_pow] using himage
  have hc : -((d^2 : ℝ) : ℂ) ∉ singularHillSpectrum (periodOneOriginal q) := by
    simpa only [ofReal_pow] using houtside
  obtain ⟨C,hpos,hC,hw⟩ := exists_miura_action_contour_positive_index q u (d^2) hi
    (n : ℕ) (by exact_mod_cast n.pos)
  exact ⟨d^2,u,C,hi,hc,hpos,(hillHminusCanonicalAction_eq_Miura_of_real q hq u (d^2) hi hc n).trans hC.symm,hw⟩

end NLS.KdV
