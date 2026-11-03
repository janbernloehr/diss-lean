import NLS.KdV.HillHminusOneMiuraActionBalls
import NLS.KdV.HillHminusOneNormalizedCanonicalDomain
import NLS.ZakharovShabat.SourceFullAbelianSymmetricAnalytic

/-! # Actual Miura balls with all symmetric spectral coordinates

The full Cauchy construction supplies midpoint and squared Dirac gap
analyticity on ONE source ball before every index. Pulling that ball back
under an actual real-preserving Miura lift gives analytic squared Hill
gaps, including every collapsed gap. The squared difference-of-squares
formula uses the SAME original Hill indices on every real input.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

structure HillHminusMiuraGapBall where
  actionBall : HillHminusMiuraActionBall
  highNeighborhood : HillHminusCanonicalHighNeighborhood
  high_subset : actionBall.source ⊆ highNeighborhood.source
  midpoint_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ
    (fun q => sourceStandardRootMidpoint (by simp) (by norm_num)
      (hillMiuraDiagonal (actionBall.lift q)) n) actionBall.source
  dirac_gap_square_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ
    (fun q => (canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal (actionBall.lift q)))
      (periodOnePotential_mem _) n)^2) actionBall.source

namespace HillHminusMiuraGapBall

def source (B : HillHminusMiuraGapBall) : Set PeriodOneHminusOne := B.actionBall.source

def diracSum (B : HillHminusMiuraGapBall) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  2*sourceStandardRootMidpoint (by simp) (by norm_num)
    (hillMiuraDiagonal (B.actionBall.lift q)) (n : ℕ)

def gapSquare (B : HillHminusMiuraGapBall) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  (canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal (B.actionBall.lift q)))
    (periodOnePotential_mem _) (n : ℕ))^2*(B.diracSum n q)^2

theorem source_open (B : HillHminusMiuraGapBall) : IsOpen B.source := B.actionBall.source_open

theorem analytic_diracSum (B : HillHminusMiuraGapBall) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.diracSum n) B.source := by
  intro q hq
  exact analyticAt_const.mul (B.midpoint_analytic (n : ℕ) q hq)

theorem analytic_gapSquare (B : HillHminusMiuraGapBall) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.gapSquare n) B.source := by
  intro q hq
  exact (B.dirac_gap_square_analytic (n : ℕ) q hq).mul ((B.analytic_diracSum n q hq).pow 2)

theorem diracSum_eq_endpoints (B : HillHminusMiuraGapBall) (n : ℕ+) (q : PeriodOneHminusOne) :
    B.diracSum n q = hillMiuraDiracRight (B.actionBall.lift q) (n : ℕ)+
      hillMiuraDiracLeft (B.actionBall.lift q) (n : ℕ) := by
  unfold diracSum sourceStandardRootMidpoint canonicalPeriodicMidpoint
  change 2*((hillMiuraDiracLeft (B.actionBall.lift q) (n : ℕ)+
    hillMiuraDiracRight (B.actionBall.lift q) (n : ℕ))/2) = _
  ring

theorem diracSum_re_pos_of_real (B : HillHminusMiuraGapBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hreal : IsRealPeriodOneHminusOne q) :
    0 < (B.diracSum n q).re := by
  let u : PeriodOneRealL2 := ⟨B.actionBall.lift q,B.actionBall.lift_real q hq hreal⟩
  have hpos := hillMiura_positive_gap_left_pos u (n : ℕ) (by exact_mod_cast n.pos)
  have hord := hillMiuraDiracPair_ordered u.val (n : ℕ)
  change 0 < (hillMiuraDiracLeft u.val (n : ℕ)).re at hpos
  rw [B.diracSum_eq_endpoints,add_re]
  change 0 < (hillMiuraDiracRight u.val (n : ℕ)).re+(hillMiuraDiracLeft u.val (n : ℕ)).re
  linarith

theorem gapSquare_eq_real (B : HillHminusMiuraGapBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hreal : IsRealPeriodOneHminusOne q) :
    B.gapSquare n q =
      ((hillHminusLabels q hreal (2*(n : ℕ)) : ℂ)-
        (hillHminusLabels q hreal (2*(n : ℕ)-1) : ℂ))^2 := by
  let u : PeriodOneRealL2 := ⟨B.actionBall.lift q,B.actionBall.lift_real q hq hreal⟩
  have he := hillHminus_gap_eq_miuraDirac_product q hreal u B.actionBall.shift
    (B.actionBall.image q hq) (B.actionBall.outside q hq) (n : ℕ) n.pos
  rw [← ofReal_sub,he,mul_pow]
  unfold gapSquare
  rw [B.diracSum_eq_endpoints]
  rfl

theorem gapSquare_eq_on_overlap (B C : HillHminusMiuraGapBall) (n : ℕ+) :
    EqOn (B.gapSquare n) (C.gapSquare n) (B.source ∩ C.source) := by
  intro q hq
  have hreal : ∃ a ∈ B.source ∩ C.source, IsRealPeriodOneHminusOne a :=
    exists_real_mem_periodOneHminus_ball_inter B.actionBall.center C.actionBall.center
      B.actionBall.center_real C.actionBall.center_real B.actionBall.radius C.actionBall.radius ⟨q,hq⟩
  exact analytic_eqOn_of_real_periodOneHminus (B.source ∩ C.source)
    (B.source_open.inter C.source_open) ((convex_ball B.actionBall.center B.actionBall.radius).inter
      (convex_ball C.actionBall.center C.actionBall.radius)).isPreconnected hreal
    (B.gapSquare n) (C.gapSquare n)
    ((B.analytic_gapSquare n).mono inter_subset_left) ((C.analytic_gapSquare n).mono inter_subset_right)
    (fun a ha har => (B.gapSquare_eq_real n a ha.1 har).trans
      (C.gapSquare_eq_real n a ha.2 har).symm) hq

end HillHminusMiuraGapBall

theorem exists_hillHminusMiuraGapBall (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ B : HillHminusMiuraGapBall, q ∈ B.source := by
  obtain ⟨B,hB⟩ := exists_hillHminusMiuraActionBall q hq
  let φ : realTypeSourceSubmodule 2 := hillMiuraRealSource ⟨B.lift q,B.lift_real q hB hq⟩
  obtain ⟨W,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies (p := 2) (by simp) (by norm_num)
  obtain ⟨C,hC⟩ := hfamilies φ
  let f : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (B.lift a)
  have hf : AnalyticOnNhd ℂ f B.source := by
    intro a ha
    exact (hillMiuraDiagonal.analyticAt (B.lift a)).comp (f := B.lift) (B.lift_analytic a ha)
  let U := B.source ∩ f ⁻¹' ball C.discs.source.val C.discs.sourceRadius
  have hU : IsOpen U := hf.continuousOn.isOpen_inter_preimage B.source_open isOpen_ball
  have hqU : q ∈ U := by
    refine ⟨hB,?_⟩
    change f q ∈ ball C.discs.source.val C.discs.sourceRadius
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨H,hqH⟩ := exists_hillHminusCanonicalHighNeighborhood q hq
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((hU.inter H.source_open).mem_nhds ⟨hqU,hqH⟩)
  let D : HillHminusMiuraActionBall := {
    center := q
    center_real := hq
    radius := r
    radius_pos := hr
    shift := B.shift
    lift := B.lift
    lift_analytic := B.lift_analytic.mono (fun a ha => (hball ha).1.1)
    lift_real := fun a ha => B.lift_real a (hball ha).1.1
    image := fun a ha => B.image a (hball ha).1.1
    outside := fun a ha => B.outside a (hball ha).1.1
    action_analytic := fun n => (B.action_analytic n).mono (fun a ha => (hball ha).1.1) }
  let E : HillHminusMiuraGapBall := {
    actionBall := D
    highNeighborhood := H
    high_subset := fun a ha => (hball ha).2
    midpoint_analytic := fun n a ha =>
      ((C.symmetric_analytic n).1 (f a) (hball ha).1.2).comp (f := f) (hf a (hball ha).1.1)
    dirac_gap_square_analytic := fun n a ha =>
      ((C.symmetric_analytic n).2 (f a) (hball ha).1.2).comp (f := f) (hf a (hball ha).1.1) }
  exact ⟨E,mem_ball_self hr⟩

end NLS.KdV
