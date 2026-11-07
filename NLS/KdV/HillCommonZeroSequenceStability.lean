import NLS.KdV.HminusOneCanonicalHillZeroSequences
import Mathlib.Analysis.Complex.Schwarz

/-! Uniform FULL-l2 stability of ALL actual Hill zero sequences near
EVERY real source. Schwarz uses the SAME graph and source radii, chosen
before all numerator indices; no uniform real continuity is assumed. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_common_canonical_zero_sequence_control
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r L M : ℝ, 0 < r ∧ 0 ≤ L ∧ 0 ≤ M ∧
      ball q r ⊆ hillHminusCanonicalZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n : ℕ+,
        dist (hillHminusCanonicalZeroSequence n y) (hillHminusPsiZeroDisplacement n ⟨q,hr⟩) ≤ L*dist y q ∧
        ‖hillHminusCanonicalZeroSequence n y‖ ≤ M := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  obtain ⟨ρ,r,hρ,hrpos,s,hs⟩ := P.exists_common_actual_analytic_zero_sequences q hq hr
  let B : HillHminusZeroSequenceBall := {
    center := q
    center_real := hr
    radius := r
    radius_pos := hrpos
    subset := fun y hy => mem_iUnion.mpr ⟨P.parent,P.subset ((hs 1).2.2.1 y hy).1.2⟩
    value := s
    analytic_value := fun n => (hs n).1
    real_eq := fun n => (hs n).2.2.2.1
    root := fun n => (hs n).2.2.2.2 }
  obtain ⟨A,hA⟩ := (isCompact_hillHminusEnergyGapData ⟨q,hr⟩).isBounded.exists_norm_le
  let M : ℝ := max A 0+ρ
  have hM : 0 ≤ M := add_nonneg (le_max_right _ _) hρ.le
  refine ⟨r,ρ/r,M,hrpos,(div_pos hρ hrpos).le,hM,(fun y hy => mem_iUnion.mpr ⟨B,hy⟩),?_⟩
  intro y hy n
  have hmaps : MapsTo (s n) (ball q r) (closedBall (s n q) ρ) := by
    intro z hz
    rw [mem_closedBall,(hs n).2.1]
    have hgraph := mem_ball.mp ((hs n).2.2.1 z hz).2.2.1
    rw [Prod.dist_eq] at hgraph
    exact ((le_max_left _ _).trans_lt hgraph).le
  have hdist := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hs n).1.differentiableOn hmaps hy
  rw [(hs n).2.1] at hdist
  have hn : ‖hillHminusPsiZeroDisplacement n ⟨q,hr⟩‖ ≤ max A 0 :=
    (hA _ (actual_hill_zero_sequence_mem_energyGapData ⟨q,hr⟩ n)).trans (le_max_left _ _)
  have hgraph := mem_ball.mp ((hs n).2.2.1 y hy).2.2.1
  rw [Prod.dist_eq] at hgraph
  have hnear : dist (s n y) (hillHminusPsiZeroDisplacement n ⟨q,hr⟩) ≤ ρ :=
    ((le_max_left _ _).trans_lt hgraph).le
  have hbound : ‖s n y‖ ≤ M := by
    calc
      _ ≤ dist (s n y) (hillHminusPsiZeroDisplacement n ⟨q,hr⟩)+‖hillHminusPsiZeroDisplacement n ⟨q,hr⟩‖ :=
        by simpa only [dist_eq_norm] using norm_le_norm_sub_add (s n y) (hillHminusPsiZeroDisplacement n ⟨q,hr⟩)
      _ ≤ M := by dsimp only [M]; linarith
  rw [B.canonical_value_eq n y hy]
  exact ⟨hdist,hbound⟩

theorem exists_common_canonical_zero_sequence_graph_radius
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ hillHminusCanonicalZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n : ℕ+,
        dist (hillHminusCanonicalZeroSequence n y,y) (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) < ε := by
  obtain ⟨R,L,_,hR,hL,_,hU,hcontrol⟩ := exists_common_canonical_zero_sequence_control q hr
  let r := min R (ε/(L+1))
  have hrpos : 0 < r := lt_min hR (div_pos hε (by positivity))
  have hrR : r ≤ R := min_le_left _ _
  refine ⟨r,hrpos,(ball_subset_ball hrR).trans hU,?_⟩
  intro y hy n
  have hsmall : (L+1)*dist y q < ε := by
    have hd : dist y q < ε/(L+1) := (mem_ball.mp hy).trans_le (min_le_right _ _)
    have h := (lt_div_iff₀ (by positivity : 0 < L+1)).mp hd
    nlinarith
  have hdist := (hcontrol y (ball_subset_ball hrR hy) n).1
  rw [Prod.dist_eq,max_lt_iff]
  constructor
  · nlinarith [dist_nonneg (x := y) (y := q)]
  · nlinarith [mul_nonneg hL (dist_nonneg (x := y) (y := q))]

theorem exists_common_zero_sequence_gapData_thickening
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ hillHminusCanonicalZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n : ℕ+,
        (hillHminusCanonicalZeroSequence n y,y) ∈
          cthickening ε (hillHminusEnergyGapData ⟨q,hr⟩ ×ˢ {q}) := by
  obtain ⟨r,hrpos,hU,hgraph⟩ := exists_common_canonical_zero_sequence_graph_radius q hr ε hε
  refine ⟨r,hrpos,hU,?_⟩
  intro y hy n
  exact mem_cthickening_of_dist_le _ (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) ε _
    ⟨actual_hill_zero_sequence_mem_energyGapData ⟨q,hr⟩ n,rfl⟩ (hgraph y hy n).le

end NLS.KdV
